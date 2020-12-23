%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:47 EST 2020

% Result     : Theorem 7.34s
% Output     : CNFRefutation 7.70s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 557 expanded)
%              Number of leaves         :   34 ( 190 expanded)
%              Depth                    :   18
%              Number of atoms          :  427 (1866 expanded)
%              Number of equality atoms :   28 (  98 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_7740,plain,(
    ! [A_664,B_665] :
      ( v3_pre_topc(k1_tops_1(A_664,B_665),A_664)
      | ~ m1_subset_1(B_665,k1_zfmisc_1(u1_struct_0(A_664)))
      | ~ l1_pre_topc(A_664)
      | ~ v2_pre_topc(A_664) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_7750,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_7740])).

tff(c_7756,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_7750])).

tff(c_7592,plain,(
    ! [A_650,B_651] :
      ( r1_tarski(k1_tops_1(A_650,B_651),B_651)
      | ~ m1_subset_1(B_651,k1_zfmisc_1(u1_struct_0(A_650)))
      | ~ l1_pre_topc(A_650) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_7600,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_7592])).

tff(c_7605,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7600])).

tff(c_6869,plain,(
    ! [A_575,B_576] :
      ( v3_pre_topc(k1_tops_1(A_575,B_576),A_575)
      | ~ m1_subset_1(B_576,k1_zfmisc_1(u1_struct_0(A_575)))
      | ~ l1_pre_topc(A_575)
      | ~ v2_pre_topc(A_575) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6877,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_6869])).

tff(c_6882,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_6877])).

tff(c_6793,plain,(
    ! [A_564,B_565] :
      ( r1_tarski(k1_tops_1(A_564,B_565),B_565)
      | ~ m1_subset_1(B_565,k1_zfmisc_1(u1_struct_0(A_564)))
      | ~ l1_pre_topc(A_564) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6801,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_6793])).

tff(c_6806,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6801])).

tff(c_6019,plain,(
    ! [A_493,B_494] :
      ( v3_pre_topc(k1_tops_1(A_493,B_494),A_493)
      | ~ m1_subset_1(B_494,k1_zfmisc_1(u1_struct_0(A_493)))
      | ~ l1_pre_topc(A_493)
      | ~ v2_pre_topc(A_493) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6027,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_6019])).

tff(c_6032,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_6027])).

tff(c_5930,plain,(
    ! [A_479,B_480] :
      ( r1_tarski(k1_tops_1(A_479,B_480),B_480)
      | ~ m1_subset_1(B_480,k1_zfmisc_1(u1_struct_0(A_479)))
      | ~ l1_pre_topc(A_479) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5938,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_5930])).

tff(c_5943,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5938])).

tff(c_5333,plain,(
    ! [A_419,B_420] :
      ( v3_pre_topc(k1_tops_1(A_419,B_420),A_419)
      | ~ m1_subset_1(B_420,k1_zfmisc_1(u1_struct_0(A_419)))
      | ~ l1_pre_topc(A_419)
      | ~ v2_pre_topc(A_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_5341,plain,
    ( v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_5333])).

tff(c_5346,plain,(
    v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_5341])).

tff(c_5188,plain,(
    ! [A_402,B_403] :
      ( r1_tarski(k1_tops_1(A_402,B_403),B_403)
      | ~ m1_subset_1(B_403,k1_zfmisc_1(u1_struct_0(A_402)))
      | ~ l1_pre_topc(A_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5196,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_5188])).

tff(c_5201,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5196])).

tff(c_54,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | v3_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_72,plain,(
    v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_50,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_69,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_46,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_71,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_58,plain,
    ( r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_100,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_238,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(k1_tops_1(A_77,B_78),B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_248,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_238])).

tff(c_256,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_248])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_206,plain,(
    ! [A_68,C_69,B_70] :
      ( m1_subset_1(A_68,C_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(C_69))
      | ~ r2_hidden(A_68,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_222,plain,(
    ! [A_73,B_74,A_75] :
      ( m1_subset_1(A_73,B_74)
      | ~ r2_hidden(A_73,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(resolution,[status(thm)],[c_10,c_206])).

tff(c_297,plain,(
    ! [A_87,B_88,B_89] :
      ( m1_subset_1(A_87,B_88)
      | ~ r1_tarski(B_89,B_88)
      | v1_xboole_0(B_89)
      | ~ m1_subset_1(A_87,B_89) ) ),
    inference(resolution,[status(thm)],[c_6,c_222])).

tff(c_314,plain,(
    ! [A_87] :
      ( m1_subset_1(A_87,'#skF_3')
      | v1_xboole_0(k1_tops_1('#skF_1','#skF_3'))
      | ~ m1_subset_1(A_87,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_256,c_297])).

tff(c_1267,plain,(
    v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_314])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_subset_1(A_3,k3_subset_1(A_3,B_4)) = B_4
      | ~ m1_subset_1(B_4,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_108,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_100,c_4])).

tff(c_28,plain,(
    ! [A_25,B_27] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_25),B_27),A_25)
      | ~ v3_pre_topc(B_27,A_25)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2197,plain,(
    ! [A_215,B_216] :
      ( k2_pre_topc(A_215,B_216) = B_216
      | ~ v4_pre_topc(B_216,A_215)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2207,plain,
    ( k2_pre_topc('#skF_1','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_100,c_2197])).

tff(c_2219,plain,
    ( k2_pre_topc('#skF_1','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2207])).

tff(c_2240,plain,(
    ~ v4_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2219])).

tff(c_2224,plain,(
    ! [A_217,B_218] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_217),B_218),A_217)
      | ~ v3_pre_topc(B_218,A_217)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ l1_pre_topc(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2231,plain,
    ( v4_pre_topc('#skF_4','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_2224])).

tff(c_2236,plain,
    ( v4_pre_topc('#skF_4','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2231])).

tff(c_2326,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2240,c_2236])).

tff(c_2327,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2326])).

tff(c_2330,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_2327])).

tff(c_2337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_2330])).

tff(c_2339,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2326])).

tff(c_16,plain,(
    ! [B_17,A_15] :
      ( v4_pre_topc(B_17,A_15)
      | k2_pre_topc(A_15,B_17) != B_17
      | ~ v2_pre_topc(A_15)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2342,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) != k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2339,c_16])).

tff(c_2361,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) != k3_subset_1(u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_2342])).

tff(c_2918,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) != k3_subset_1(u1_struct_0('#skF_1'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2361])).

tff(c_18,plain,(
    ! [A_15,B_17] :
      ( k2_pre_topc(A_15,B_17) = B_17
      | ~ v4_pre_topc(B_17,A_15)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2345,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2339,c_18])).

tff(c_2364,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2345])).

tff(c_2988,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_2918,c_2364])).

tff(c_2991,plain,
    ( ~ v3_pre_topc('#skF_4','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_2988])).

tff(c_2995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_100,c_72,c_2991])).

tff(c_2997,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_2361])).

tff(c_20,plain,(
    ! [A_18,B_20] :
      ( k3_subset_1(u1_struct_0(A_18),k2_pre_topc(A_18,k3_subset_1(u1_struct_0(A_18),B_20))) = k1_tops_1(A_18,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3007,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k1_tops_1('#skF_1','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2997,c_20])).

tff(c_3011,plain,(
    k1_tops_1('#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_100,c_108,c_3007])).

tff(c_32,plain,(
    ! [A_31,B_35,C_37] :
      ( r1_tarski(k1_tops_1(A_31,B_35),k1_tops_1(A_31,C_37))
      | ~ r1_tarski(B_35,C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3032,plain,(
    ! [C_37] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_1',C_37))
      | ~ r1_tarski('#skF_4',C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3011,c_32])).

tff(c_3213,plain,(
    ! [C_266] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_1',C_266))
      | ~ r1_tarski('#skF_4',C_266)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_100,c_3032])).

tff(c_3237,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_3213])).

tff(c_3250,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_3237])).

tff(c_73,plain,(
    ! [C_53,B_54,A_55] :
      ( ~ v1_xboole_0(C_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(C_53))
      | ~ r2_hidden(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_88,plain,(
    ! [B_58,A_59,A_60] :
      ( ~ v1_xboole_0(B_58)
      | ~ r2_hidden(A_59,A_60)
      | ~ r1_tarski(A_60,B_58) ) ),
    inference(resolution,[status(thm)],[c_10,c_73])).

tff(c_93,plain,(
    ! [B_58] :
      ( ~ v1_xboole_0(B_58)
      | ~ r1_tarski('#skF_4',B_58) ) ),
    inference(resolution,[status(thm)],[c_71,c_88])).

tff(c_3260,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_3250,c_93])).

tff(c_3272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1267,c_3260])).

tff(c_3274,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_314])).

tff(c_40,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_3304,plain,(
    ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_3307,plain,
    ( v1_xboole_0(k1_tops_1('#skF_1','#skF_3'))
    | ~ m1_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_3304])).

tff(c_3310,plain,(
    ~ m1_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_3274,c_3307])).

tff(c_3275,plain,(
    ! [A_267,B_268] :
      ( k2_pre_topc(A_267,B_268) = B_268
      | ~ v4_pre_topc(B_268,A_267)
      | ~ m1_subset_1(B_268,k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ l1_pre_topc(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3285,plain,
    ( k2_pre_topc('#skF_1','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_100,c_3275])).

tff(c_3297,plain,
    ( k2_pre_topc('#skF_1','#skF_4') = '#skF_4'
    | ~ v4_pre_topc('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3285])).

tff(c_3303,plain,(
    ~ v4_pre_topc('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3297])).

tff(c_4163,plain,(
    ! [A_328,B_329] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_328),B_329),A_328)
      | ~ v3_pre_topc(B_329,A_328)
      | ~ m1_subset_1(B_329,k1_zfmisc_1(u1_struct_0(A_328)))
      | ~ l1_pre_topc(A_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4174,plain,
    ( v4_pre_topc('#skF_4','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_4163])).

tff(c_4179,plain,
    ( v4_pre_topc('#skF_4','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4174])).

tff(c_4180,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_3303,c_4179])).

tff(c_4251,plain,(
    ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4180])).

tff(c_4289,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_2,c_4251])).

tff(c_4296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_4289])).

tff(c_4298,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_4180])).

tff(c_4301,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_4298,c_18])).

tff(c_4317,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4301])).

tff(c_4755,plain,(
    ~ v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4317])).

tff(c_4758,plain,
    ( ~ v3_pre_topc('#skF_4','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_4755])).

tff(c_4762,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_100,c_72,c_4758])).

tff(c_4763,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k3_subset_1(u1_struct_0('#skF_1'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_4317])).

tff(c_4774,plain,
    ( k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_4')) = k1_tops_1('#skF_1','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4763,c_20])).

tff(c_4778,plain,(
    k1_tops_1('#skF_1','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_100,c_108,c_4774])).

tff(c_4820,plain,(
    ! [C_37] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_1',C_37))
      | ~ r1_tarski('#skF_4',C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4778,c_32])).

tff(c_4894,plain,(
    ! [C_369] :
      ( r1_tarski('#skF_4',k1_tops_1('#skF_1',C_369))
      | ~ r1_tarski('#skF_4',C_369)
      | ~ m1_subset_1(C_369,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_100,c_4820])).

tff(c_4918,plain,
    ( r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_4894])).

tff(c_4931,plain,(
    r1_tarski('#skF_4',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_4918])).

tff(c_227,plain,(
    ! [B_74] :
      ( m1_subset_1('#skF_2',B_74)
      | ~ r1_tarski('#skF_4',B_74) ) ),
    inference(resolution,[status(thm)],[c_71,c_222])).

tff(c_4938,plain,(
    m1_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4931,c_227])).

tff(c_4950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3310,c_4938])).

tff(c_5036,plain,(
    ! [D_379] :
      ( ~ r2_hidden('#skF_2',D_379)
      | ~ r1_tarski(D_379,'#skF_3')
      | ~ v3_pre_topc(D_379,'#skF_1')
      | ~ m1_subset_1(D_379,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_5047,plain,
    ( ~ r2_hidden('#skF_2','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_100,c_5036])).

tff(c_5062,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_69,c_71,c_5047])).

tff(c_5063,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_5347,plain,(
    ! [A_421,B_422] :
      ( m1_subset_1(k1_tops_1(A_421,B_422),k1_zfmisc_1(u1_struct_0(A_421)))
      | ~ m1_subset_1(B_422,k1_zfmisc_1(u1_struct_0(A_421)))
      | ~ l1_pre_topc(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5064,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_5284,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5064,c_56])).

tff(c_5353,plain,(
    ! [B_422] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_422))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_422),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_422),'#skF_1')
      | ~ m1_subset_1(B_422,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_5347,c_5284])).

tff(c_5747,plain,(
    ! [B_449] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_449))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_449),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_449),'#skF_1')
      | ~ m1_subset_1(B_449,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5353])).

tff(c_5765,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_5747])).

tff(c_5777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5346,c_5201,c_5063,c_5765])).

tff(c_5778,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_6069,plain,(
    ! [A_500,B_501] :
      ( m1_subset_1(k1_tops_1(A_500,B_501),k1_zfmisc_1(u1_struct_0(A_500)))
      | ~ m1_subset_1(B_501,k1_zfmisc_1(u1_struct_0(A_500)))
      | ~ l1_pre_topc(A_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5779,plain,(
    ~ v3_pre_topc('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | v3_pre_topc('#skF_4','#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_5862,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5779,c_52])).

tff(c_6080,plain,(
    ! [B_501] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_501))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_501),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_501),'#skF_1')
      | ~ m1_subset_1(B_501,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6069,c_5862])).

tff(c_6624,plain,(
    ! [B_534] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_534))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_534),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_534),'#skF_1')
      | ~ m1_subset_1(B_534,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6080])).

tff(c_6642,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_6624])).

tff(c_6654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6032,c_5943,c_5778,c_6642])).

tff(c_6655,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_6917,plain,(
    ! [A_581,B_582] :
      ( m1_subset_1(k1_tops_1(A_581,B_582),k1_zfmisc_1(u1_struct_0(A_581)))
      | ~ m1_subset_1(B_582,k1_zfmisc_1(u1_struct_0(A_581)))
      | ~ l1_pre_topc(A_581) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6656,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r2_hidden('#skF_2','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_6884,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6656,c_44])).

tff(c_6921,plain,(
    ! [B_582] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_582))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_582),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_582),'#skF_1')
      | ~ m1_subset_1(B_582,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6917,c_6884])).

tff(c_7423,plain,(
    ! [B_615] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_615))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_615),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_615),'#skF_1')
      | ~ m1_subset_1(B_615,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6921])).

tff(c_7441,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_7423])).

tff(c_7453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6882,c_6806,c_6655,c_7441])).

tff(c_7454,plain,(
    r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_7660,plain,(
    ! [A_656,B_657] :
      ( m1_subset_1(k1_tops_1(A_656,B_657),k1_zfmisc_1(u1_struct_0(A_656)))
      | ~ m1_subset_1(B_657,k1_zfmisc_1(u1_struct_0(A_656)))
      | ~ l1_pre_topc(A_656) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_7455,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_48,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | r1_tarski('#skF_4','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_7620,plain,(
    ! [D_46] :
      ( ~ r2_hidden('#skF_2',D_46)
      | ~ r1_tarski(D_46,'#skF_3')
      | ~ v3_pre_topc(D_46,'#skF_1')
      | ~ m1_subset_1(D_46,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_7455,c_48])).

tff(c_7664,plain,(
    ! [B_657] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_657))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_657),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_657),'#skF_1')
      | ~ m1_subset_1(B_657,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_7660,c_7620])).

tff(c_8209,plain,(
    ! [B_699] :
      ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1',B_699))
      | ~ r1_tarski(k1_tops_1('#skF_1',B_699),'#skF_3')
      | ~ v3_pre_topc(k1_tops_1('#skF_1',B_699),'#skF_1')
      | ~ m1_subset_1(B_699,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7664])).

tff(c_8227,plain,
    ( ~ r2_hidden('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k1_tops_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_8209])).

tff(c_8239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7756,c_7605,c_7454,c_8227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:05:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.34/2.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.34/2.52  
% 7.34/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.34/2.52  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.34/2.52  
% 7.34/2.52  %Foreground sorts:
% 7.34/2.52  
% 7.34/2.52  
% 7.34/2.52  %Background operators:
% 7.34/2.52  
% 7.34/2.52  
% 7.34/2.52  %Foreground operators:
% 7.34/2.52  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.34/2.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.34/2.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.34/2.52  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.34/2.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.34/2.52  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.34/2.52  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.34/2.52  tff('#skF_2', type, '#skF_2': $i).
% 7.34/2.52  tff('#skF_3', type, '#skF_3': $i).
% 7.34/2.52  tff('#skF_1', type, '#skF_1': $i).
% 7.34/2.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.34/2.52  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.34/2.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.34/2.52  tff('#skF_4', type, '#skF_4': $i).
% 7.34/2.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.34/2.52  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.34/2.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.34/2.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.34/2.52  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.34/2.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.34/2.52  
% 7.70/2.56  tff(f_139, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tops_1)).
% 7.70/2.56  tff(f_92, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 7.70/2.56  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 7.70/2.56  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 7.70/2.56  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.70/2.56  tff(f_49, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 7.70/2.56  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 7.70/2.56  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tops_1)).
% 7.70/2.56  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 7.70/2.56  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 7.70/2.56  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 7.70/2.56  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 7.70/2.56  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 7.70/2.56  tff(f_84, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 7.70/2.56  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.70/2.56  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.70/2.56  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.70/2.56  tff(c_7740, plain, (![A_664, B_665]: (v3_pre_topc(k1_tops_1(A_664, B_665), A_664) | ~m1_subset_1(B_665, k1_zfmisc_1(u1_struct_0(A_664))) | ~l1_pre_topc(A_664) | ~v2_pre_topc(A_664))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.70/2.56  tff(c_7750, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_7740])).
% 7.70/2.56  tff(c_7756, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_7750])).
% 7.70/2.56  tff(c_7592, plain, (![A_650, B_651]: (r1_tarski(k1_tops_1(A_650, B_651), B_651) | ~m1_subset_1(B_651, k1_zfmisc_1(u1_struct_0(A_650))) | ~l1_pre_topc(A_650))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.70/2.56  tff(c_7600, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_7592])).
% 7.70/2.56  tff(c_7605, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7600])).
% 7.70/2.56  tff(c_6869, plain, (![A_575, B_576]: (v3_pre_topc(k1_tops_1(A_575, B_576), A_575) | ~m1_subset_1(B_576, k1_zfmisc_1(u1_struct_0(A_575))) | ~l1_pre_topc(A_575) | ~v2_pre_topc(A_575))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.70/2.56  tff(c_6877, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_6869])).
% 7.70/2.56  tff(c_6882, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_6877])).
% 7.70/2.56  tff(c_6793, plain, (![A_564, B_565]: (r1_tarski(k1_tops_1(A_564, B_565), B_565) | ~m1_subset_1(B_565, k1_zfmisc_1(u1_struct_0(A_564))) | ~l1_pre_topc(A_564))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.70/2.56  tff(c_6801, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_6793])).
% 7.70/2.56  tff(c_6806, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6801])).
% 7.70/2.56  tff(c_6019, plain, (![A_493, B_494]: (v3_pre_topc(k1_tops_1(A_493, B_494), A_493) | ~m1_subset_1(B_494, k1_zfmisc_1(u1_struct_0(A_493))) | ~l1_pre_topc(A_493) | ~v2_pre_topc(A_493))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.70/2.56  tff(c_6027, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_6019])).
% 7.70/2.56  tff(c_6032, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_6027])).
% 7.70/2.56  tff(c_5930, plain, (![A_479, B_480]: (r1_tarski(k1_tops_1(A_479, B_480), B_480) | ~m1_subset_1(B_480, k1_zfmisc_1(u1_struct_0(A_479))) | ~l1_pre_topc(A_479))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.70/2.56  tff(c_5938, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_5930])).
% 7.70/2.56  tff(c_5943, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_5938])).
% 7.70/2.56  tff(c_5333, plain, (![A_419, B_420]: (v3_pre_topc(k1_tops_1(A_419, B_420), A_419) | ~m1_subset_1(B_420, k1_zfmisc_1(u1_struct_0(A_419))) | ~l1_pre_topc(A_419) | ~v2_pre_topc(A_419))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.70/2.56  tff(c_5341, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_5333])).
% 7.70/2.56  tff(c_5346, plain, (v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_5341])).
% 7.70/2.56  tff(c_5188, plain, (![A_402, B_403]: (r1_tarski(k1_tops_1(A_402, B_403), B_403) | ~m1_subset_1(B_403, k1_zfmisc_1(u1_struct_0(A_402))) | ~l1_pre_topc(A_402))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.70/2.56  tff(c_5196, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_5188])).
% 7.70/2.56  tff(c_5201, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_5196])).
% 7.70/2.56  tff(c_54, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | v3_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.70/2.56  tff(c_72, plain, (v3_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_54])).
% 7.70/2.56  tff(c_50, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.70/2.56  tff(c_69, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 7.70/2.56  tff(c_46, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.70/2.56  tff(c_71, plain, (r2_hidden('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_46])).
% 7.70/2.56  tff(c_58, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.70/2.56  tff(c_100, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_58])).
% 7.70/2.56  tff(c_238, plain, (![A_77, B_78]: (r1_tarski(k1_tops_1(A_77, B_78), B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.70/2.56  tff(c_248, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_238])).
% 7.70/2.56  tff(c_256, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_248])).
% 7.70/2.56  tff(c_6, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.70/2.56  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.70/2.56  tff(c_206, plain, (![A_68, C_69, B_70]: (m1_subset_1(A_68, C_69) | ~m1_subset_1(B_70, k1_zfmisc_1(C_69)) | ~r2_hidden(A_68, B_70))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.70/2.56  tff(c_222, plain, (![A_73, B_74, A_75]: (m1_subset_1(A_73, B_74) | ~r2_hidden(A_73, A_75) | ~r1_tarski(A_75, B_74))), inference(resolution, [status(thm)], [c_10, c_206])).
% 7.70/2.56  tff(c_297, plain, (![A_87, B_88, B_89]: (m1_subset_1(A_87, B_88) | ~r1_tarski(B_89, B_88) | v1_xboole_0(B_89) | ~m1_subset_1(A_87, B_89))), inference(resolution, [status(thm)], [c_6, c_222])).
% 7.70/2.56  tff(c_314, plain, (![A_87]: (m1_subset_1(A_87, '#skF_3') | v1_xboole_0(k1_tops_1('#skF_1', '#skF_3')) | ~m1_subset_1(A_87, k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_256, c_297])).
% 7.70/2.56  tff(c_1267, plain, (v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_314])).
% 7.70/2.56  tff(c_4, plain, (![A_3, B_4]: (k3_subset_1(A_3, k3_subset_1(A_3, B_4))=B_4 | ~m1_subset_1(B_4, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.70/2.56  tff(c_108, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_100, c_4])).
% 7.70/2.56  tff(c_28, plain, (![A_25, B_27]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_25), B_27), A_25) | ~v3_pre_topc(B_27, A_25) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.70/2.56  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.70/2.56  tff(c_2197, plain, (![A_215, B_216]: (k2_pre_topc(A_215, B_216)=B_216 | ~v4_pre_topc(B_216, A_215) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_pre_topc(A_215))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.70/2.56  tff(c_2207, plain, (k2_pre_topc('#skF_1', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_100, c_2197])).
% 7.70/2.56  tff(c_2219, plain, (k2_pre_topc('#skF_1', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2207])).
% 7.70/2.56  tff(c_2240, plain, (~v4_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_2219])).
% 7.70/2.56  tff(c_2224, plain, (![A_217, B_218]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_217), B_218), A_217) | ~v3_pre_topc(B_218, A_217) | ~m1_subset_1(B_218, k1_zfmisc_1(u1_struct_0(A_217))) | ~l1_pre_topc(A_217))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.70/2.56  tff(c_2231, plain, (v4_pre_topc('#skF_4', '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_108, c_2224])).
% 7.70/2.56  tff(c_2236, plain, (v4_pre_topc('#skF_4', '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2231])).
% 7.70/2.56  tff(c_2326, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_2240, c_2236])).
% 7.70/2.56  tff(c_2327, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_2326])).
% 7.70/2.56  tff(c_2330, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_2327])).
% 7.70/2.56  tff(c_2337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_2330])).
% 7.70/2.56  tff(c_2339, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_2326])).
% 7.70/2.56  tff(c_16, plain, (![B_17, A_15]: (v4_pre_topc(B_17, A_15) | k2_pre_topc(A_15, B_17)!=B_17 | ~v2_pre_topc(A_15) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.70/2.56  tff(c_2342, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))!=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4') | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2339, c_16])).
% 7.70/2.56  tff(c_2361, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))!=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_2342])).
% 7.70/2.56  tff(c_2918, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))!=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4')), inference(splitLeft, [status(thm)], [c_2361])).
% 7.70/2.56  tff(c_18, plain, (![A_15, B_17]: (k2_pre_topc(A_15, B_17)=B_17 | ~v4_pre_topc(B_17, A_15) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.70/2.56  tff(c_2345, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2339, c_18])).
% 7.70/2.56  tff(c_2364, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2345])).
% 7.70/2.56  tff(c_2988, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_2918, c_2364])).
% 7.70/2.56  tff(c_2991, plain, (~v3_pre_topc('#skF_4', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_2988])).
% 7.70/2.56  tff(c_2995, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_100, c_72, c_2991])).
% 7.70/2.56  tff(c_2997, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4')), inference(splitRight, [status(thm)], [c_2361])).
% 7.70/2.56  tff(c_20, plain, (![A_18, B_20]: (k3_subset_1(u1_struct_0(A_18), k2_pre_topc(A_18, k3_subset_1(u1_struct_0(A_18), B_20)))=k1_tops_1(A_18, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.70/2.56  tff(c_3007, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k1_tops_1('#skF_1', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2997, c_20])).
% 7.70/2.56  tff(c_3011, plain, (k1_tops_1('#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_100, c_108, c_3007])).
% 7.70/2.56  tff(c_32, plain, (![A_31, B_35, C_37]: (r1_tarski(k1_tops_1(A_31, B_35), k1_tops_1(A_31, C_37)) | ~r1_tarski(B_35, C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.70/2.56  tff(c_3032, plain, (![C_37]: (r1_tarski('#skF_4', k1_tops_1('#skF_1', C_37)) | ~r1_tarski('#skF_4', C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3011, c_32])).
% 7.70/2.56  tff(c_3213, plain, (![C_266]: (r1_tarski('#skF_4', k1_tops_1('#skF_1', C_266)) | ~r1_tarski('#skF_4', C_266) | ~m1_subset_1(C_266, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_100, c_3032])).
% 7.70/2.56  tff(c_3237, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_3213])).
% 7.70/2.56  tff(c_3250, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_3237])).
% 7.70/2.56  tff(c_73, plain, (![C_53, B_54, A_55]: (~v1_xboole_0(C_53) | ~m1_subset_1(B_54, k1_zfmisc_1(C_53)) | ~r2_hidden(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.70/2.56  tff(c_88, plain, (![B_58, A_59, A_60]: (~v1_xboole_0(B_58) | ~r2_hidden(A_59, A_60) | ~r1_tarski(A_60, B_58))), inference(resolution, [status(thm)], [c_10, c_73])).
% 7.70/2.56  tff(c_93, plain, (![B_58]: (~v1_xboole_0(B_58) | ~r1_tarski('#skF_4', B_58))), inference(resolution, [status(thm)], [c_71, c_88])).
% 7.70/2.56  tff(c_3260, plain, (~v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_3250, c_93])).
% 7.70/2.56  tff(c_3272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1267, c_3260])).
% 7.70/2.56  tff(c_3274, plain, (~v1_xboole_0(k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_314])).
% 7.70/2.56  tff(c_40, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.70/2.56  tff(c_3304, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_40])).
% 7.70/2.56  tff(c_3307, plain, (v1_xboole_0(k1_tops_1('#skF_1', '#skF_3')) | ~m1_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_6, c_3304])).
% 7.70/2.56  tff(c_3310, plain, (~m1_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_3274, c_3307])).
% 7.70/2.56  tff(c_3275, plain, (![A_267, B_268]: (k2_pre_topc(A_267, B_268)=B_268 | ~v4_pre_topc(B_268, A_267) | ~m1_subset_1(B_268, k1_zfmisc_1(u1_struct_0(A_267))) | ~l1_pre_topc(A_267))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.70/2.56  tff(c_3285, plain, (k2_pre_topc('#skF_1', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_100, c_3275])).
% 7.70/2.56  tff(c_3297, plain, (k2_pre_topc('#skF_1', '#skF_4')='#skF_4' | ~v4_pre_topc('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_3285])).
% 7.70/2.56  tff(c_3303, plain, (~v4_pre_topc('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_3297])).
% 7.70/2.56  tff(c_4163, plain, (![A_328, B_329]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_328), B_329), A_328) | ~v3_pre_topc(B_329, A_328) | ~m1_subset_1(B_329, k1_zfmisc_1(u1_struct_0(A_328))) | ~l1_pre_topc(A_328))), inference(cnfTransformation, [status(thm)], [f_101])).
% 7.70/2.56  tff(c_4174, plain, (v4_pre_topc('#skF_4', '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_108, c_4163])).
% 7.70/2.56  tff(c_4179, plain, (v4_pre_topc('#skF_4', '#skF_1') | ~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4174])).
% 7.70/2.56  tff(c_4180, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_3303, c_4179])).
% 7.70/2.56  tff(c_4251, plain, (~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_4180])).
% 7.70/2.56  tff(c_4289, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_2, c_4251])).
% 7.70/2.56  tff(c_4296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_4289])).
% 7.70/2.56  tff(c_4298, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_4180])).
% 7.70/2.56  tff(c_4301, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_4298, c_18])).
% 7.70/2.56  tff(c_4317, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4') | ~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4301])).
% 7.70/2.56  tff(c_4755, plain, (~v4_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_4317])).
% 7.70/2.56  tff(c_4758, plain, (~v3_pre_topc('#skF_4', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_4755])).
% 7.70/2.56  tff(c_4762, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_100, c_72, c_4758])).
% 7.70/2.56  tff(c_4763, plain, (k2_pre_topc('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k3_subset_1(u1_struct_0('#skF_1'), '#skF_4')), inference(splitRight, [status(thm)], [c_4317])).
% 7.70/2.56  tff(c_4774, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_4'))=k1_tops_1('#skF_1', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4763, c_20])).
% 7.70/2.56  tff(c_4778, plain, (k1_tops_1('#skF_1', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_100, c_108, c_4774])).
% 7.70/2.56  tff(c_4820, plain, (![C_37]: (r1_tarski('#skF_4', k1_tops_1('#skF_1', C_37)) | ~r1_tarski('#skF_4', C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4778, c_32])).
% 7.70/2.56  tff(c_4894, plain, (![C_369]: (r1_tarski('#skF_4', k1_tops_1('#skF_1', C_369)) | ~r1_tarski('#skF_4', C_369) | ~m1_subset_1(C_369, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_100, c_4820])).
% 7.70/2.56  tff(c_4918, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_4894])).
% 7.70/2.56  tff(c_4931, plain, (r1_tarski('#skF_4', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_4918])).
% 7.70/2.56  tff(c_227, plain, (![B_74]: (m1_subset_1('#skF_2', B_74) | ~r1_tarski('#skF_4', B_74))), inference(resolution, [status(thm)], [c_71, c_222])).
% 7.70/2.56  tff(c_4938, plain, (m1_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_4931, c_227])).
% 7.70/2.56  tff(c_4950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3310, c_4938])).
% 7.70/2.56  tff(c_5036, plain, (![D_379]: (~r2_hidden('#skF_2', D_379) | ~r1_tarski(D_379, '#skF_3') | ~v3_pre_topc(D_379, '#skF_1') | ~m1_subset_1(D_379, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_40])).
% 7.70/2.56  tff(c_5047, plain, (~r2_hidden('#skF_2', '#skF_4') | ~r1_tarski('#skF_4', '#skF_3') | ~v3_pre_topc('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_100, c_5036])).
% 7.70/2.56  tff(c_5062, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_69, c_71, c_5047])).
% 7.70/2.56  tff(c_5063, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_58])).
% 7.70/2.56  tff(c_5347, plain, (![A_421, B_422]: (m1_subset_1(k1_tops_1(A_421, B_422), k1_zfmisc_1(u1_struct_0(A_421))) | ~m1_subset_1(B_422, k1_zfmisc_1(u1_struct_0(A_421))) | ~l1_pre_topc(A_421))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.70/2.56  tff(c_5064, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_58])).
% 7.70/2.56  tff(c_56, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))) | m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.70/2.56  tff(c_5284, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_5064, c_56])).
% 7.70/2.56  tff(c_5353, plain, (![B_422]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_422)) | ~r1_tarski(k1_tops_1('#skF_1', B_422), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_422), '#skF_1') | ~m1_subset_1(B_422, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_5347, c_5284])).
% 7.70/2.56  tff(c_5747, plain, (![B_449]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_449)) | ~r1_tarski(k1_tops_1('#skF_1', B_449), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_449), '#skF_1') | ~m1_subset_1(B_449, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_5353])).
% 7.70/2.56  tff(c_5765, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_34, c_5747])).
% 7.70/2.56  tff(c_5777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5346, c_5201, c_5063, c_5765])).
% 7.70/2.56  tff(c_5778, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_54])).
% 7.70/2.56  tff(c_6069, plain, (![A_500, B_501]: (m1_subset_1(k1_tops_1(A_500, B_501), k1_zfmisc_1(u1_struct_0(A_500))) | ~m1_subset_1(B_501, k1_zfmisc_1(u1_struct_0(A_500))) | ~l1_pre_topc(A_500))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.70/2.56  tff(c_5779, plain, (~v3_pre_topc('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 7.70/2.56  tff(c_52, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))) | v3_pre_topc('#skF_4', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.70/2.56  tff(c_5862, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_5779, c_52])).
% 7.70/2.56  tff(c_6080, plain, (![B_501]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_501)) | ~r1_tarski(k1_tops_1('#skF_1', B_501), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_501), '#skF_1') | ~m1_subset_1(B_501, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_6069, c_5862])).
% 7.70/2.56  tff(c_6624, plain, (![B_534]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_534)) | ~r1_tarski(k1_tops_1('#skF_1', B_534), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_534), '#skF_1') | ~m1_subset_1(B_534, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6080])).
% 7.70/2.56  tff(c_6642, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_34, c_6624])).
% 7.70/2.56  tff(c_6654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6032, c_5943, c_5778, c_6642])).
% 7.70/2.56  tff(c_6655, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_46])).
% 7.70/2.56  tff(c_6917, plain, (![A_581, B_582]: (m1_subset_1(k1_tops_1(A_581, B_582), k1_zfmisc_1(u1_struct_0(A_581))) | ~m1_subset_1(B_582, k1_zfmisc_1(u1_struct_0(A_581))) | ~l1_pre_topc(A_581))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.70/2.56  tff(c_6656, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_46])).
% 7.70/2.56  tff(c_44, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r2_hidden('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.70/2.56  tff(c_6884, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_6656, c_44])).
% 7.70/2.56  tff(c_6921, plain, (![B_582]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_582)) | ~r1_tarski(k1_tops_1('#skF_1', B_582), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_582), '#skF_1') | ~m1_subset_1(B_582, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_6917, c_6884])).
% 7.70/2.56  tff(c_7423, plain, (![B_615]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_615)) | ~r1_tarski(k1_tops_1('#skF_1', B_615), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_615), '#skF_1') | ~m1_subset_1(B_615, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6921])).
% 7.70/2.56  tff(c_7441, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_34, c_7423])).
% 7.70/2.56  tff(c_7453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6882, c_6806, c_6655, c_7441])).
% 7.70/2.56  tff(c_7454, plain, (r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_50])).
% 7.70/2.56  tff(c_7660, plain, (![A_656, B_657]: (m1_subset_1(k1_tops_1(A_656, B_657), k1_zfmisc_1(u1_struct_0(A_656))) | ~m1_subset_1(B_657, k1_zfmisc_1(u1_struct_0(A_656))) | ~l1_pre_topc(A_656))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.70/2.56  tff(c_7455, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 7.70/2.56  tff(c_48, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))) | r1_tarski('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 7.70/2.56  tff(c_7620, plain, (![D_46]: (~r2_hidden('#skF_2', D_46) | ~r1_tarski(D_46, '#skF_3') | ~v3_pre_topc(D_46, '#skF_1') | ~m1_subset_1(D_46, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_7455, c_48])).
% 7.70/2.56  tff(c_7664, plain, (![B_657]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_657)) | ~r1_tarski(k1_tops_1('#skF_1', B_657), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_657), '#skF_1') | ~m1_subset_1(B_657, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_7660, c_7620])).
% 7.70/2.56  tff(c_8209, plain, (![B_699]: (~r2_hidden('#skF_2', k1_tops_1('#skF_1', B_699)) | ~r1_tarski(k1_tops_1('#skF_1', B_699), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', B_699), '#skF_1') | ~m1_subset_1(B_699, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7664])).
% 7.70/2.56  tff(c_8227, plain, (~r2_hidden('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~v3_pre_topc(k1_tops_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_34, c_8209])).
% 7.70/2.56  tff(c_8239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7756, c_7605, c_7454, c_8227])).
% 7.70/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.70/2.56  
% 7.70/2.56  Inference rules
% 7.70/2.56  ----------------------
% 7.70/2.56  #Ref     : 0
% 7.70/2.56  #Sup     : 1833
% 7.70/2.56  #Fact    : 0
% 7.70/2.56  #Define  : 0
% 7.70/2.56  #Split   : 91
% 7.70/2.56  #Chain   : 0
% 7.70/2.56  #Close   : 0
% 7.70/2.56  
% 7.70/2.56  Ordering : KBO
% 7.70/2.56  
% 7.70/2.56  Simplification rules
% 7.70/2.56  ----------------------
% 7.70/2.56  #Subsume      : 391
% 7.70/2.56  #Demod        : 1102
% 7.70/2.56  #Tautology    : 401
% 7.70/2.56  #SimpNegUnit  : 131
% 7.70/2.56  #BackRed      : 15
% 7.70/2.56  
% 7.70/2.56  #Partial instantiations: 0
% 7.70/2.56  #Strategies tried      : 1
% 7.70/2.56  
% 7.70/2.56  Timing (in seconds)
% 7.70/2.56  ----------------------
% 7.70/2.57  Preprocessing        : 0.33
% 7.70/2.57  Parsing              : 0.19
% 7.70/2.57  CNF conversion       : 0.02
% 7.70/2.57  Main loop            : 1.43
% 7.70/2.57  Inferencing          : 0.51
% 7.70/2.57  Reduction            : 0.46
% 7.70/2.57  Demodulation         : 0.32
% 7.70/2.57  BG Simplification    : 0.05
% 7.70/2.57  Subsumption          : 0.29
% 7.70/2.57  Abstraction          : 0.06
% 7.70/2.57  MUC search           : 0.00
% 7.70/2.57  Cooper               : 0.00
% 7.70/2.57  Total                : 1.83
% 7.70/2.57  Index Insertion      : 0.00
% 7.70/2.57  Index Deletion       : 0.00
% 7.70/2.57  Index Matching       : 0.00
% 7.70/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
