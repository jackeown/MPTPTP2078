%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1124+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:26 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 201 expanded)
%              Number of leaves         :   33 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 ( 466 expanded)
%              Number of equality atoms :    7 (  30 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_28,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_58,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_40,plain,(
    ! [A_48] :
      ( l1_struct_0(A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_62,plain,(
    ! [A_63] :
      ( u1_struct_0(A_63) = k2_struct_0(A_63)
      | ~ l1_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_67,plain,(
    ! [A_64] :
      ( u1_struct_0(A_64) = k2_struct_0(A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_40,c_62])).

tff(c_71,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_67])).

tff(c_50,plain,(
    ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_72,plain,(
    ~ m1_subset_1('#skF_7',k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_50])).

tff(c_54,plain,(
    m1_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_78,plain,(
    ! [B_66,A_67] :
      ( l1_pre_topc(B_66)
      | ~ m1_pre_topc(B_66,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_81,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_78])).

tff(c_84,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_81])).

tff(c_66,plain,(
    ! [A_48] :
      ( u1_struct_0(A_48) = k2_struct_0(A_48)
      | ~ l1_pre_topc(A_48) ) ),
    inference(resolution,[status(thm)],[c_40,c_62])).

tff(c_88,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_84,c_66])).

tff(c_96,plain,(
    ! [A_72] :
      ( m1_subset_1(k2_struct_0(A_72),k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_99,plain,
    ( m1_subset_1(k2_struct_0('#skF_6'),k1_zfmisc_1(k2_struct_0('#skF_6')))
    | ~ l1_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_96])).

tff(c_137,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_140,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_137])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_140])).

tff(c_146,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_89,plain,(
    m1_subset_1('#skF_7',k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_52])).

tff(c_28,plain,(
    ! [B_29,A_7] :
      ( r1_tarski(k2_struct_0(B_29),k2_struct_0(A_7))
      | ~ m1_pre_topc(B_29,A_7)
      | ~ l1_pre_topc(B_29)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_46,plain,(
    ! [A_53,B_54] :
      ( r2_hidden(A_53,B_54)
      | v1_xboole_0(B_54)
      | ~ m1_subset_1(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_130,plain,(
    ! [C_76,B_77,A_78] :
      ( r2_hidden(C_76,B_77)
      | ~ r2_hidden(C_76,A_78)
      | ~ r1_tarski(A_78,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_221,plain,(
    ! [A_93,B_94,B_95] :
      ( r2_hidden(A_93,B_94)
      | ~ r1_tarski(B_95,B_94)
      | v1_xboole_0(B_95)
      | ~ m1_subset_1(A_93,B_95) ) ),
    inference(resolution,[status(thm)],[c_46,c_130])).

tff(c_384,plain,(
    ! [A_122,A_123,B_124] :
      ( r2_hidden(A_122,k2_struct_0(A_123))
      | v1_xboole_0(k2_struct_0(B_124))
      | ~ m1_subset_1(A_122,k2_struct_0(B_124))
      | ~ m1_pre_topc(B_124,A_123)
      | ~ l1_pre_topc(B_124)
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_28,c_221])).

tff(c_394,plain,(
    ! [A_123] :
      ( r2_hidden('#skF_7',k2_struct_0(A_123))
      | v1_xboole_0(k2_struct_0('#skF_6'))
      | ~ m1_pre_topc('#skF_6',A_123)
      | ~ l1_pre_topc('#skF_6')
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_89,c_384])).

tff(c_409,plain,(
    ! [A_123] :
      ( r2_hidden('#skF_7',k2_struct_0(A_123))
      | v1_xboole_0(k2_struct_0('#skF_6'))
      | ~ m1_pre_topc('#skF_6',A_123)
      | ~ l1_pre_topc(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_394])).

tff(c_410,plain,(
    v1_xboole_0(k2_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_409])).

tff(c_44,plain,(
    ! [A_52] :
      ( ~ v1_xboole_0(k2_struct_0(A_52))
      | ~ l1_struct_0(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_413,plain,
    ( ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_410,c_44])).

tff(c_416,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_413])).

tff(c_418,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_416])).

tff(c_425,plain,(
    ! [A_128] :
      ( r2_hidden('#skF_7',k2_struct_0(A_128))
      | ~ m1_pre_topc('#skF_6',A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(splitRight,[status(thm)],[c_409])).

tff(c_102,plain,
    ( m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_96])).

tff(c_103,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_106,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_103])).

tff(c_110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_106])).

tff(c_111,plain,(
    m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_152,plain,(
    ! [A_79,C_80,B_81] :
      ( m1_subset_1(A_79,C_80)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(C_80))
      | ~ r2_hidden(A_79,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_160,plain,(
    ! [A_79] :
      ( m1_subset_1(A_79,k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_79,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_111,c_152])).

tff(c_432,plain,
    ( m1_subset_1('#skF_7',k2_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_425,c_160])).

tff(c_442,plain,(
    m1_subset_1('#skF_7',k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_432])).

tff(c_444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_442])).

%------------------------------------------------------------------------------
