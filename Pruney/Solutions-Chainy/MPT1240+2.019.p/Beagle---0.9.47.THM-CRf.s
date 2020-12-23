%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:48 EST 2020

% Result     : Theorem 7.53s
% Output     : CNFRefutation 7.53s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 441 expanded)
%              Number of leaves         :   31 ( 152 expanded)
%              Depth                    :   17
%              Number of atoms          :  328 (1369 expanded)
%              Number of equality atoms :   20 (  56 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B,C] :
            ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_hidden(B,k1_tops_1(A,C))
            <=> ? [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                  & v3_pre_topc(D,A)
                  & r1_tarski(D,C)
                  & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_56,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_64,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_56])).

tff(c_6664,plain,(
    ! [A_449,C_450,B_451] :
      ( r1_tarski(A_449,C_450)
      | ~ r1_tarski(B_451,C_450)
      | ~ r1_tarski(A_449,B_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6669,plain,(
    ! [A_449] :
      ( r1_tarski(A_449,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_449,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_64,c_6664])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6304,plain,(
    ! [A_409,B_410] :
      ( r1_tarski(k1_tops_1(A_409,B_410),B_410)
      | ~ m1_subset_1(B_410,k1_zfmisc_1(u1_struct_0(A_409)))
      | ~ l1_pre_topc(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6312,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_6304])).

tff(c_6317,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6312])).

tff(c_5744,plain,(
    ! [A_331,C_332,B_333] :
      ( r1_tarski(A_331,C_332)
      | ~ r1_tarski(B_333,C_332)
      | ~ r1_tarski(A_331,B_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5747,plain,(
    ! [A_331] :
      ( r1_tarski(A_331,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_331,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_64,c_5744])).

tff(c_46,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_67,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_68,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,C_49)
      | ~ r1_tarski(B_50,C_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_48] :
      ( r1_tarski(A_48,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_48,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_64,c_68])).

tff(c_50,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | v3_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_65,plain,(
    v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_42,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_66,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_54,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_110,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_129,plain,(
    ! [C_60,A_61,B_62] :
      ( r2_hidden(C_60,A_61)
      | ~ r2_hidden(C_60,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_146,plain,(
    ! [A_65] :
      ( r2_hidden('#skF_2',A_65)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_65)) ) ),
    inference(resolution,[status(thm)],[c_66,c_129])).

tff(c_155,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_2',B_13)
      | ~ r1_tarski('#skF_4',B_13) ) ),
    inference(resolution,[status(thm)],[c_12,c_146])).

tff(c_36,plain,(
    ! [D_43] :
      ( ~ r2_hidden('#skF_2',D_43)
      | ~ r1_tarski(D_43,'#skF_3')
      | ~ v3_pre_topc(D_43,'#skF_1')
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3012,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_3020,plain,(
    ~ r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_155,c_3012])).

tff(c_133,plain,(
    ! [A_63,B_64] :
      ( k3_subset_1(A_63,k3_subset_1(A_63,B_64)) = B_64
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_142,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_110,c_133])).

tff(c_24,plain,(
    ! [A_22,B_24] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_22),B_24),A_22)
      | ~ v3_pre_topc(B_24,A_22)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(k3_subset_1(A_4,B_5),k1_zfmisc_1(A_4))
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2856,plain,(
    ! [A_202,B_203] :
      ( k2_pre_topc(A_202,B_203) = B_203
      | ~ v4_pre_topc(B_203,A_202)
      | ~ m1_subset_1(B_203,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ l1_pre_topc(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2859,plain,
    ( k2_pre_topc('#skF_1','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_110,c_2856])).

tff(c_2873,plain,
    ( k2_pre_topc('#skF_1','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2859])).

tff(c_2880,plain,(
    ~ v4_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2873])).

tff(c_3219,plain,(
    ! [A_236,B_237] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_236),B_237),A_236)
      | ~ v3_pre_topc(B_237,A_236)
      | ~ m1_subset_1(B_237,k1_zfmisc_1(u1_struct_0(A_236)))
      | ~ l1_pre_topc(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3233,plain,
    ( v4_pre_topc('#skF_4','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_3219])).

tff(c_3242,plain,
    ( v4_pre_topc('#skF_4','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3233])).

tff(c_3243,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2880,c_3242])).

tff(c_4127,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3243])).

tff(c_4130,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_4,c_4127])).

tff(c_4137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_4130])).

tff(c_4139,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_3243])).

tff(c_14,plain,(
    ! [B_16,A_14] :
      ( v4_pre_topc(B_16,A_14)
      | k2_pre_topc(A_14,B_16) != B_16
      | ~ v2_pre_topc(A_14)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4155,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) != k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4139,c_14])).

tff(c_4178,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) != k3_subset_1(u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_4155])).

tff(c_5316,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) != k3_subset_1(u1_struct_0('#skF_1'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4178])).

tff(c_16,plain,(
    ! [A_14,B_16] :
      ( k2_pre_topc(A_14,B_16) = B_16
      | ~ v4_pre_topc(B_16,A_14)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4161,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4139,c_16])).

tff(c_4183,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4161])).

tff(c_5317,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_5316,c_4183])).

tff(c_5329,plain,
    ( ~ v3_pre_topc('#skF_4','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_5317])).

tff(c_5338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_110,c_65,c_5329])).

tff(c_5340,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_4178])).

tff(c_18,plain,(
    ! [A_17,B_19] :
      ( k3_subset_1(u1_struct_0(A_17),k2_pre_topc(A_17,k3_subset_1(u1_struct_0(A_17),B_19))) = k1_tops_1(A_17,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5412,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k1_tops_1('#skF_1','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5340,c_18])).

tff(c_5426,plain,(
    k1_tops_1('#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_110,c_142,c_5412])).

tff(c_28,plain,(
    ! [A_28,B_32,C_34] :
      ( r1_tarski(k1_tops_1(A_28,B_32),k1_tops_1(A_28,C_34))
      | ~ r1_tarski(B_32,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5484,plain,(
    ! [C_34] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_1',C_34))
      | ~ r1_tarski('#skF_4',C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5426,c_28])).

tff(c_5672,plain,(
    ! [C_329] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_1',C_329))
      | ~ r1_tarski('#skF_4',C_329)
      | ~ m1_subset_1(C_329,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_110,c_5484])).

tff(c_5692,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_5672])).

tff(c_5702,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_5692])).

tff(c_5704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3020,c_5702])).

tff(c_5710,plain,(
    ! [D_330] :
      ( ~ r2_hidden('#skF_2',D_330)
      | ~ r1_tarski(D_330,'#skF_3')
      | ~ v3_pre_topc(D_330,'#skF_1')
      | ~ m1_subset_1(D_330,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_5713,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_110,c_5710])).

tff(c_5728,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_67,c_66,c_5713])).

tff(c_5730,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_5734,plain,(
    ~ r1_tarski('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_5730])).

tff(c_5737,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_5734])).

tff(c_5741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_5737])).

tff(c_5742,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_5753,plain,(
    ! [C_335,A_336,B_337] :
      ( r2_hidden(C_335,A_336)
      | ~ r2_hidden(C_335,B_337)
      | ~ m1_subset_1(B_337,k1_zfmisc_1(A_336)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_5770,plain,(
    ! [A_340] :
      ( r2_hidden('#skF_2',A_340)
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(A_340)) ) ),
    inference(resolution,[status(thm)],[c_5742,c_5753])).

tff(c_5776,plain,(
    ! [B_341] :
      ( r2_hidden('#skF_2',B_341)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),B_341) ) ),
    inference(resolution,[status(thm)],[c_12,c_5770])).

tff(c_5781,plain,
    ( r2_hidden('#skF_2',u1_struct_0('#skF_1'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_5747,c_5776])).

tff(c_5791,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5781])).

tff(c_5878,plain,(
    ! [A_354,B_355] :
      ( r1_tarski(k1_tops_1(A_354,B_355),B_355)
      | ~ m1_subset_1(B_355,k1_zfmisc_1(u1_struct_0(A_354)))
      | ~ l1_pre_topc(A_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5886,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_5878])).

tff(c_5891,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_5886])).

tff(c_5893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5791,c_5891])).

tff(c_5895,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_5781])).

tff(c_6168,plain,(
    ! [A_388,B_389] :
      ( v3_pre_topc(k1_tops_1(A_388,B_389),A_388)
      | ~ m1_subset_1(B_389,k1_zfmisc_1(u1_struct_0(A_388)))
      | ~ l1_pre_topc(A_388)
      | ~ v2_pre_topc(A_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6176,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_6168])).

tff(c_6181,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_6176])).

tff(c_5743,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,(
    ! [D_43] :
      ( ~ r2_hidden('#skF_2',D_43)
      | ~ r1_tarski(D_43,'#skF_3')
      | ~ v3_pre_topc(D_43,'#skF_1')
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r1_tarski('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6020,plain,(
    ! [D_367] :
      ( ~ r2_hidden('#skF_2',D_367)
      | ~ r1_tarski(D_367,'#skF_3')
      | ~ v3_pre_topc(D_367,'#skF_1')
      | ~ m1_subset_1(D_367,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5743,c_44])).

tff(c_6147,plain,(
    ! [A_387] :
      ( ~ r2_hidden('#skF_2',A_387)
      | ~ r1_tarski(A_387,'#skF_3')
      | ~ v3_pre_topc(A_387,'#skF_1')
      | ~ r1_tarski(A_387,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_12,c_6020])).

tff(c_6182,plain,(
    ! [A_390] :
      ( ~ r2_hidden('#skF_2',A_390)
      | ~ v3_pre_topc(A_390,'#skF_1')
      | ~ r1_tarski(A_390,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_5747,c_6147])).

tff(c_6185,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6181,c_6182])).

tff(c_6192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5895,c_5742,c_6185])).

tff(c_6193,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_6395,plain,(
    ! [A_417,B_418] :
      ( v3_pre_topc(k1_tops_1(A_417,B_418),A_417)
      | ~ m1_subset_1(B_418,k1_zfmisc_1(u1_struct_0(A_417)))
      | ~ l1_pre_topc(A_417)
      | ~ v2_pre_topc(A_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6403,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_6395])).

tff(c_6408,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_6403])).

tff(c_6196,plain,(
    ! [A_391,C_392,B_393] :
      ( r1_tarski(A_391,C_392)
      | ~ r1_tarski(B_393,C_392)
      | ~ r1_tarski(A_391,B_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6202,plain,(
    ! [A_391] :
      ( r1_tarski(A_391,u1_struct_0('#skF_1'))
      | ~ r1_tarski(A_391,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_64,c_6196])).

tff(c_6194,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,(
    ! [D_43] :
      ( ~ r2_hidden('#skF_2',D_43)
      | ~ r1_tarski(D_43,'#skF_3')
      | ~ v3_pre_topc(D_43,'#skF_1')
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r2_hidden('#skF_2','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6338,plain,(
    ! [D_413] :
      ( ~ r2_hidden('#skF_2',D_413)
      | ~ r1_tarski(D_413,'#skF_3')
      | ~ v3_pre_topc(D_413,'#skF_1')
      | ~ m1_subset_1(D_413,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6194,c_40])).

tff(c_6621,plain,(
    ! [A_447] :
      ( ~ r2_hidden('#skF_2',A_447)
      | ~ r1_tarski(A_447,'#skF_3')
      | ~ v3_pre_topc(A_447,'#skF_1')
      | ~ r1_tarski(A_447,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_12,c_6338])).

tff(c_6642,plain,(
    ! [A_448] :
      ( ~ r2_hidden('#skF_2',A_448)
      | ~ v3_pre_topc(A_448,'#skF_1')
      | ~ r1_tarski(A_448,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6202,c_6621])).

tff(c_6649,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6408,c_6642])).

tff(c_6659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6317,c_6193,c_6649])).

tff(c_6660,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_6696,plain,(
    ! [C_456,A_457,B_458] :
      ( r2_hidden(C_456,A_457)
      | ~ r2_hidden(C_456,B_458)
      | ~ m1_subset_1(B_458,k1_zfmisc_1(A_457)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6700,plain,(
    ! [A_459] :
      ( r2_hidden('#skF_2',A_459)
      | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_3'),k1_zfmisc_1(A_459)) ) ),
    inference(resolution,[status(thm)],[c_6660,c_6696])).

tff(c_6706,plain,(
    ! [B_460] :
      ( r2_hidden('#skF_2',B_460)
      | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),B_460) ) ),
    inference(resolution,[status(thm)],[c_12,c_6700])).

tff(c_6715,plain,
    ( r2_hidden('#skF_2',u1_struct_0('#skF_1'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6669,c_6706])).

tff(c_6774,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_6715])).

tff(c_6836,plain,(
    ! [A_472,B_473] :
      ( r1_tarski(k1_tops_1(A_472,B_473),B_473)
      | ~ m1_subset_1(B_473,k1_zfmisc_1(u1_struct_0(A_472)))
      | ~ l1_pre_topc(A_472) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6844,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_6836])).

tff(c_6849,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_6844])).

tff(c_6851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6774,c_6849])).

tff(c_6853,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_6715])).

tff(c_7011,plain,(
    ! [A_491,B_492] :
      ( v3_pre_topc(k1_tops_1(A_491,B_492),A_491)
      | ~ m1_subset_1(B_492,k1_zfmisc_1(u1_struct_0(A_491)))
      | ~ l1_pre_topc(A_491)
      | ~ v2_pre_topc(A_491) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_7019,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_7011])).

tff(c_7024,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_7019])).

tff(c_6661,plain,(
    ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [D_43] :
      ( ~ r2_hidden('#skF_2',D_43)
      | ~ r1_tarski(D_43,'#skF_3')
      | ~ v3_pre_topc(D_43,'#skF_1')
      | ~ m1_subset_1(D_43,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v3_pre_topc('#skF_4','#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6730,plain,(
    ! [D_463] :
      ( ~ r2_hidden('#skF_2',D_463)
      | ~ r1_tarski(D_463,'#skF_3')
      | ~ v3_pre_topc(D_463,'#skF_1')
      | ~ m1_subset_1(D_463,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6661,c_48])).

tff(c_7091,plain,(
    ! [A_502] :
      ( ~ r2_hidden('#skF_2',A_502)
      | ~ r1_tarski(A_502,'#skF_3')
      | ~ v3_pre_topc(A_502,'#skF_1')
      | ~ r1_tarski(A_502,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_12,c_6730])).

tff(c_7112,plain,(
    ! [A_503] :
      ( ~ r2_hidden('#skF_2',A_503)
      | ~ v3_pre_topc(A_503,'#skF_1')
      | ~ r1_tarski(A_503,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_6669,c_7091])).

tff(c_7115,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_7024,c_7112])).

tff(c_7119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6853,c_6660,c_7115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:34:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.53/2.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.53/2.53  
% 7.53/2.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.53/2.53  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.53/2.53  
% 7.53/2.53  %Foreground sorts:
% 7.53/2.53  
% 7.53/2.53  
% 7.53/2.53  %Background operators:
% 7.53/2.53  
% 7.53/2.53  
% 7.53/2.53  %Foreground operators:
% 7.53/2.53  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.53/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.53/2.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.53/2.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.53/2.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.53/2.53  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.53/2.53  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.53/2.53  tff('#skF_2', type, '#skF_2': $i).
% 7.53/2.53  tff('#skF_3', type, '#skF_3': $i).
% 7.53/2.53  tff('#skF_1', type, '#skF_1': $i).
% 7.53/2.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.53/2.53  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.53/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.53/2.53  tff('#skF_4', type, '#skF_4': $i).
% 7.53/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.53/2.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.53/2.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.53/2.53  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.53/2.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.53/2.53  
% 7.53/2.56  tff(f_127, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 7.53/2.56  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.53/2.56  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.53/2.56  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 7.53/2.56  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 7.53/2.56  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 7.53/2.56  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 7.53/2.56  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 7.53/2.56  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 7.53/2.56  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 7.53/2.56  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 7.53/2.56  tff(f_80, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 7.53/2.56  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.53/2.56  tff(c_56, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.53/2.56  tff(c_64, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_56])).
% 7.53/2.56  tff(c_6664, plain, (![A_449, C_450, B_451]: (r1_tarski(A_449, C_450) | ~r1_tarski(B_451, C_450) | ~r1_tarski(A_449, B_451))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.53/2.56  tff(c_6669, plain, (![A_449]: (r1_tarski(A_449, u1_struct_0('#skF_1')) | ~r1_tarski(A_449, '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_6664])).
% 7.53/2.56  tff(c_12, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.53/2.56  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.53/2.56  tff(c_6304, plain, (![A_409, B_410]: (r1_tarski(k1_tops_1(A_409, B_410), B_410) | ~m1_subset_1(B_410, k1_zfmisc_1(u1_struct_0(A_409))) | ~l1_pre_topc(A_409))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.53/2.56  tff(c_6312, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_6304])).
% 7.53/2.56  tff(c_6317, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6312])).
% 7.53/2.56  tff(c_5744, plain, (![A_331, C_332, B_333]: (r1_tarski(A_331, C_332) | ~r1_tarski(B_333, C_332) | ~r1_tarski(A_331, B_333))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.53/2.56  tff(c_5747, plain, (![A_331]: (r1_tarski(A_331, u1_struct_0('#skF_1')) | ~r1_tarski(A_331, '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_5744])).
% 7.53/2.56  tff(c_46, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.53/2.56  tff(c_67, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 7.53/2.56  tff(c_68, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, C_49) | ~r1_tarski(B_50, C_49) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.53/2.56  tff(c_74, plain, (![A_48]: (r1_tarski(A_48, u1_struct_0('#skF_1')) | ~r1_tarski(A_48, '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_68])).
% 7.53/2.56  tff(c_50, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | v3_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.53/2.56  tff(c_65, plain, (v3_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 7.53/2.56  tff(c_42, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.53/2.56  tff(c_66, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_42])).
% 7.53/2.56  tff(c_54, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.53/2.56  tff(c_110, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_54])).
% 7.53/2.56  tff(c_129, plain, (![C_60, A_61, B_62]: (r2_hidden(C_60, A_61) | ~r2_hidden(C_60, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.53/2.56  tff(c_146, plain, (![A_65]: (r2_hidden('#skF_2', A_65) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_65)))), inference(resolution, [status(thm)], [c_66, c_129])).
% 7.53/2.56  tff(c_155, plain, (![B_13]: (r2_hidden('#skF_2', B_13) | ~r1_tarski('#skF_4', B_13))), inference(resolution, [status(thm)], [c_12, c_146])).
% 7.53/2.56  tff(c_36, plain, (![D_43]: (~r2_hidden('#skF_2', D_43) | ~r1_tarski(D_43, '#skF_3') | ~v3_pre_topc(D_43, '#skF_1') | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.53/2.56  tff(c_3012, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_36])).
% 7.53/2.56  tff(c_3020, plain, (~r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_155, c_3012])).
% 7.53/2.56  tff(c_133, plain, (![A_63, B_64]: (k3_subset_1(A_63, k3_subset_1(A_63, B_64))=B_64 | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.53/2.56  tff(c_142, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_110, c_133])).
% 7.53/2.56  tff(c_24, plain, (![A_22, B_24]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_22), B_24), A_22) | ~v3_pre_topc(B_24, A_22) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.53/2.56  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.53/2.56  tff(c_4, plain, (![A_4, B_5]: (m1_subset_1(k3_subset_1(A_4, B_5), k1_zfmisc_1(A_4)) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.53/2.56  tff(c_2856, plain, (![A_202, B_203]: (k2_pre_topc(A_202, B_203)=B_203 | ~v4_pre_topc(B_203, A_202) | ~m1_subset_1(B_203, k1_zfmisc_1(u1_struct_0(A_202))) | ~l1_pre_topc(A_202))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.53/2.56  tff(c_2859, plain, (k2_pre_topc('#skF_1', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_110, c_2856])).
% 7.53/2.56  tff(c_2873, plain, (k2_pre_topc('#skF_1', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2859])).
% 7.53/2.56  tff(c_2880, plain, (~v4_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_2873])).
% 7.53/2.56  tff(c_3219, plain, (![A_236, B_237]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_236), B_237), A_236) | ~v3_pre_topc(B_237, A_236) | ~m1_subset_1(B_237, k1_zfmisc_1(u1_struct_0(A_236))) | ~l1_pre_topc(A_236))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.53/2.56  tff(c_3233, plain, (v4_pre_topc('#skF_4', '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_142, c_3219])).
% 7.53/2.56  tff(c_3242, plain, (v4_pre_topc('#skF_4', '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3233])).
% 7.53/2.56  tff(c_3243, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_2880, c_3242])).
% 7.53/2.56  tff(c_4127, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_3243])).
% 7.53/2.56  tff(c_4130, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_4, c_4127])).
% 7.53/2.56  tff(c_4137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_4130])).
% 7.53/2.56  tff(c_4139, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_3243])).
% 7.53/2.56  tff(c_14, plain, (![B_16, A_14]: (v4_pre_topc(B_16, A_14) | k2_pre_topc(A_14, B_16)!=B_16 | ~v2_pre_topc(A_14) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.53/2.56  tff(c_4155, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))!=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4') | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4139, c_14])).
% 7.53/2.56  tff(c_4178, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))!=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_4155])).
% 7.53/2.56  tff(c_5316, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))!=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4')), inference(splitLeft, [status(thm)], [c_4178])).
% 7.53/2.56  tff(c_16, plain, (![A_14, B_16]: (k2_pre_topc(A_14, B_16)=B_16 | ~v4_pre_topc(B_16, A_14) | ~m1_subset_1(B_16, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.53/2.56  tff(c_4161, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4139, c_16])).
% 7.53/2.56  tff(c_4183, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4161])).
% 7.53/2.56  tff(c_5317, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_5316, c_4183])).
% 7.53/2.56  tff(c_5329, plain, (~v3_pre_topc('#skF_4', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_5317])).
% 7.53/2.56  tff(c_5338, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_110, c_65, c_5329])).
% 7.53/2.56  tff(c_5340, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4')), inference(splitRight, [status(thm)], [c_4178])).
% 7.53/2.56  tff(c_18, plain, (![A_17, B_19]: (k3_subset_1(u1_struct_0(A_17), k2_pre_topc(A_17, k3_subset_1(u1_struct_0(A_17), B_19)))=k1_tops_1(A_17, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.53/2.56  tff(c_5412, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k1_tops_1('#skF_1', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5340, c_18])).
% 7.53/2.56  tff(c_5426, plain, (k1_tops_1('#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_110, c_142, c_5412])).
% 7.53/2.56  tff(c_28, plain, (![A_28, B_32, C_34]: (r1_tarski(k1_tops_1(A_28, B_32), k1_tops_1(A_28, C_34)) | ~r1_tarski(B_32, C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.53/2.56  tff(c_5484, plain, (![C_34]: (r1_tarski('#skF_4', k1_tops_1('#skF_1', C_34)) | ~r1_tarski('#skF_4', C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5426, c_28])).
% 7.53/2.56  tff(c_5672, plain, (![C_329]: (r1_tarski('#skF_4', k1_tops_1('#skF_1', C_329)) | ~r1_tarski('#skF_4', C_329) | ~m1_subset_1(C_329, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_110, c_5484])).
% 7.53/2.56  tff(c_5692, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_5672])).
% 7.53/2.56  tff(c_5702, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_5692])).
% 7.53/2.56  tff(c_5704, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3020, c_5702])).
% 7.53/2.56  tff(c_5710, plain, (![D_330]: (~r2_hidden('#skF_2', D_330) | ~r1_tarski(D_330, '#skF_3') | ~v3_pre_topc(D_330, '#skF_1') | ~m1_subset_1(D_330, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_36])).
% 7.53/2.56  tff(c_5713, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_110, c_5710])).
% 7.53/2.56  tff(c_5728, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_67, c_66, c_5713])).
% 7.53/2.56  tff(c_5730, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_54])).
% 7.53/2.56  tff(c_5734, plain, (~r1_tarski('#skF_4', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_5730])).
% 7.53/2.56  tff(c_5737, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_5734])).
% 7.53/2.56  tff(c_5741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_5737])).
% 7.53/2.56  tff(c_5742, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_46])).
% 7.53/2.56  tff(c_5753, plain, (![C_335, A_336, B_337]: (r2_hidden(C_335, A_336) | ~r2_hidden(C_335, B_337) | ~m1_subset_1(B_337, k1_zfmisc_1(A_336)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.53/2.56  tff(c_5770, plain, (![A_340]: (r2_hidden('#skF_2', A_340) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(A_340)))), inference(resolution, [status(thm)], [c_5742, c_5753])).
% 7.53/2.56  tff(c_5776, plain, (![B_341]: (r2_hidden('#skF_2', B_341) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), B_341))), inference(resolution, [status(thm)], [c_12, c_5770])).
% 7.53/2.56  tff(c_5781, plain, (r2_hidden('#skF_2', u1_struct_0('#skF_1')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_5747, c_5776])).
% 7.53/2.56  tff(c_5791, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_5781])).
% 7.53/2.56  tff(c_5878, plain, (![A_354, B_355]: (r1_tarski(k1_tops_1(A_354, B_355), B_355) | ~m1_subset_1(B_355, k1_zfmisc_1(u1_struct_0(A_354))) | ~l1_pre_topc(A_354))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.53/2.56  tff(c_5886, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_5878])).
% 7.53/2.56  tff(c_5891, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_5886])).
% 7.53/2.56  tff(c_5893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5791, c_5891])).
% 7.53/2.56  tff(c_5895, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_5781])).
% 7.53/2.56  tff(c_6168, plain, (![A_388, B_389]: (v3_pre_topc(k1_tops_1(A_388, B_389), A_388) | ~m1_subset_1(B_389, k1_zfmisc_1(u1_struct_0(A_388))) | ~l1_pre_topc(A_388) | ~v2_pre_topc(A_388))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.53/2.56  tff(c_6176, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_6168])).
% 7.53/2.56  tff(c_6181, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_6176])).
% 7.53/2.56  tff(c_5743, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 7.53/2.56  tff(c_44, plain, (![D_43]: (~r2_hidden('#skF_2', D_43) | ~r1_tarski(D_43, '#skF_3') | ~v3_pre_topc(D_43, '#skF_1') | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r1_tarski('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.53/2.56  tff(c_6020, plain, (![D_367]: (~r2_hidden('#skF_2', D_367) | ~r1_tarski(D_367, '#skF_3') | ~v3_pre_topc(D_367, '#skF_1') | ~m1_subset_1(D_367, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_5743, c_44])).
% 7.53/2.56  tff(c_6147, plain, (![A_387]: (~r2_hidden('#skF_2', A_387) | ~r1_tarski(A_387, '#skF_3') | ~v3_pre_topc(A_387, '#skF_1') | ~r1_tarski(A_387, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_6020])).
% 7.53/2.56  tff(c_6182, plain, (![A_390]: (~r2_hidden('#skF_2', A_390) | ~v3_pre_topc(A_390, '#skF_1') | ~r1_tarski(A_390, '#skF_3'))), inference(resolution, [status(thm)], [c_5747, c_6147])).
% 7.53/2.56  tff(c_6185, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_6181, c_6182])).
% 7.53/2.56  tff(c_6192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5895, c_5742, c_6185])).
% 7.53/2.56  tff(c_6193, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_42])).
% 7.53/2.56  tff(c_6395, plain, (![A_417, B_418]: (v3_pre_topc(k1_tops_1(A_417, B_418), A_417) | ~m1_subset_1(B_418, k1_zfmisc_1(u1_struct_0(A_417))) | ~l1_pre_topc(A_417) | ~v2_pre_topc(A_417))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.53/2.56  tff(c_6403, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_6395])).
% 7.53/2.56  tff(c_6408, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_6403])).
% 7.53/2.56  tff(c_6196, plain, (![A_391, C_392, B_393]: (r1_tarski(A_391, C_392) | ~r1_tarski(B_393, C_392) | ~r1_tarski(A_391, B_393))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.53/2.56  tff(c_6202, plain, (![A_391]: (r1_tarski(A_391, u1_struct_0('#skF_1')) | ~r1_tarski(A_391, '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_6196])).
% 7.53/2.56  tff(c_6194, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 7.53/2.56  tff(c_40, plain, (![D_43]: (~r2_hidden('#skF_2', D_43) | ~r1_tarski(D_43, '#skF_3') | ~v3_pre_topc(D_43, '#skF_1') | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r2_hidden('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.53/2.56  tff(c_6338, plain, (![D_413]: (~r2_hidden('#skF_2', D_413) | ~r1_tarski(D_413, '#skF_3') | ~v3_pre_topc(D_413, '#skF_1') | ~m1_subset_1(D_413, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_6194, c_40])).
% 7.53/2.56  tff(c_6621, plain, (![A_447]: (~r2_hidden('#skF_2', A_447) | ~r1_tarski(A_447, '#skF_3') | ~v3_pre_topc(A_447, '#skF_1') | ~r1_tarski(A_447, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_6338])).
% 7.53/2.56  tff(c_6642, plain, (![A_448]: (~r2_hidden('#skF_2', A_448) | ~v3_pre_topc(A_448, '#skF_1') | ~r1_tarski(A_448, '#skF_3'))), inference(resolution, [status(thm)], [c_6202, c_6621])).
% 7.53/2.56  tff(c_6649, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_6408, c_6642])).
% 7.53/2.56  tff(c_6659, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6317, c_6193, c_6649])).
% 7.53/2.56  tff(c_6660, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_50])).
% 7.53/2.56  tff(c_6696, plain, (![C_456, A_457, B_458]: (r2_hidden(C_456, A_457) | ~r2_hidden(C_456, B_458) | ~m1_subset_1(B_458, k1_zfmisc_1(A_457)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.53/2.56  tff(c_6700, plain, (![A_459]: (r2_hidden('#skF_2', A_459) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_3'), k1_zfmisc_1(A_459)))), inference(resolution, [status(thm)], [c_6660, c_6696])).
% 7.53/2.56  tff(c_6706, plain, (![B_460]: (r2_hidden('#skF_2', B_460) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), B_460))), inference(resolution, [status(thm)], [c_12, c_6700])).
% 7.53/2.56  tff(c_6715, plain, (r2_hidden('#skF_2', u1_struct_0('#skF_1')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_6669, c_6706])).
% 7.53/2.56  tff(c_6774, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_6715])).
% 7.53/2.56  tff(c_6836, plain, (![A_472, B_473]: (r1_tarski(k1_tops_1(A_472, B_473), B_473) | ~m1_subset_1(B_473, k1_zfmisc_1(u1_struct_0(A_472))) | ~l1_pre_topc(A_472))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.53/2.56  tff(c_6844, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_6836])).
% 7.53/2.56  tff(c_6849, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_6844])).
% 7.53/2.56  tff(c_6851, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6774, c_6849])).
% 7.53/2.56  tff(c_6853, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_6715])).
% 7.53/2.56  tff(c_7011, plain, (![A_491, B_492]: (v3_pre_topc(k1_tops_1(A_491, B_492), A_491) | ~m1_subset_1(B_492, k1_zfmisc_1(u1_struct_0(A_491))) | ~l1_pre_topc(A_491) | ~v2_pre_topc(A_491))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.53/2.56  tff(c_7019, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_7011])).
% 7.53/2.56  tff(c_7024, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_7019])).
% 7.53/2.56  tff(c_6661, plain, (~v3_pre_topc('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_50])).
% 7.53/2.56  tff(c_48, plain, (![D_43]: (~r2_hidden('#skF_2', D_43) | ~r1_tarski(D_43, '#skF_3') | ~v3_pre_topc(D_43, '#skF_1') | ~m1_subset_1(D_43, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v3_pre_topc('#skF_4', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 7.53/2.56  tff(c_6730, plain, (![D_463]: (~r2_hidden('#skF_2', D_463) | ~r1_tarski(D_463, '#skF_3') | ~v3_pre_topc(D_463, '#skF_1') | ~m1_subset_1(D_463, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_6661, c_48])).
% 7.53/2.56  tff(c_7091, plain, (![A_502]: (~r2_hidden('#skF_2', A_502) | ~r1_tarski(A_502, '#skF_3') | ~v3_pre_topc(A_502, '#skF_1') | ~r1_tarski(A_502, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_12, c_6730])).
% 7.53/2.56  tff(c_7112, plain, (![A_503]: (~r2_hidden('#skF_2', A_503) | ~v3_pre_topc(A_503, '#skF_1') | ~r1_tarski(A_503, '#skF_3'))), inference(resolution, [status(thm)], [c_6669, c_7091])).
% 7.53/2.56  tff(c_7115, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_7024, c_7112])).
% 7.53/2.56  tff(c_7119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6853, c_6660, c_7115])).
% 7.53/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.53/2.56  
% 7.53/2.56  Inference rules
% 7.53/2.56  ----------------------
% 7.53/2.56  #Ref     : 0
% 7.53/2.56  #Sup     : 1577
% 7.53/2.56  #Fact    : 0
% 7.53/2.56  #Define  : 0
% 7.53/2.56  #Split   : 55
% 7.53/2.56  #Chain   : 0
% 7.53/2.56  #Close   : 0
% 7.53/2.56  
% 7.53/2.56  Ordering : KBO
% 7.53/2.56  
% 7.53/2.56  Simplification rules
% 7.53/2.56  ----------------------
% 7.53/2.56  #Subsume      : 547
% 7.53/2.56  #Demod        : 1002
% 7.53/2.56  #Tautology    : 289
% 7.53/2.56  #SimpNegUnit  : 47
% 7.53/2.56  #BackRed      : 26
% 7.53/2.56  
% 7.53/2.56  #Partial instantiations: 0
% 7.53/2.56  #Strategies tried      : 1
% 7.53/2.56  
% 7.53/2.56  Timing (in seconds)
% 7.53/2.56  ----------------------
% 7.53/2.56  Preprocessing        : 0.31
% 7.53/2.56  Parsing              : 0.18
% 7.53/2.56  CNF conversion       : 0.02
% 7.53/2.56  Main loop            : 1.46
% 7.53/2.56  Inferencing          : 0.48
% 7.53/2.56  Reduction            : 0.47
% 7.53/2.56  Demodulation         : 0.32
% 7.53/2.56  BG Simplification    : 0.04
% 7.53/2.56  Subsumption          : 0.37
% 7.53/2.56  Abstraction          : 0.06
% 7.53/2.56  MUC search           : 0.00
% 7.53/2.56  Cooper               : 0.00
% 7.53/2.56  Total                : 1.83
% 7.53/2.56  Index Insertion      : 0.00
% 7.53/2.56  Index Deletion       : 0.00
% 7.53/2.56  Index Matching       : 0.00
% 7.53/2.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
