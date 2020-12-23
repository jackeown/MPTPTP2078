%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1082+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:22 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   43 (  53 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 119 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(m1_funct_2,type,(
    m1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => m1_funct_2(k1_funct_2(A,B),A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_funct_2)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ( m1_funct_2(C,A,B)
      <=> ! [D] :
            ( m1_subset_1(D,C)
           => ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r2_hidden(C,k1_funct_2(A,B))
     => ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ v1_xboole_0(k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_funct_2)).

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_45,plain,(
    ! [A_34,B_35,C_36] :
      ( m1_subset_1('#skF_1'(A_34,B_35,C_36),C_36)
      | m1_funct_2(C_36,A_34,B_35)
      | v1_xboole_0(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_27,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [C_11,A_9,B_10] :
      ( v1_funct_1(C_11)
      | ~ r2_hidden(C_11,k1_funct_2(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_32,plain,(
    ! [A_19,A_9,B_10] :
      ( v1_funct_1(A_19)
      | v1_xboole_0(k1_funct_2(A_9,B_10))
      | ~ m1_subset_1(A_19,k1_funct_2(A_9,B_10)) ) ),
    inference(resolution,[status(thm)],[c_27,c_18])).

tff(c_52,plain,(
    ! [A_34,B_35,A_9,B_10] :
      ( v1_funct_1('#skF_1'(A_34,B_35,k1_funct_2(A_9,B_10)))
      | m1_funct_2(k1_funct_2(A_9,B_10),A_34,B_35)
      | v1_xboole_0(k1_funct_2(A_9,B_10)) ) ),
    inference(resolution,[status(thm)],[c_45,c_32])).

tff(c_4,plain,(
    ! [A_1,B_2,C_3] :
      ( m1_subset_1('#skF_1'(A_1,B_2,C_3),C_3)
      | m1_funct_2(C_3,A_1,B_2)
      | v1_xboole_0(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r2_hidden(A_12,B_13)
      | v1_xboole_0(B_13)
      | ~ m1_subset_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_33,plain,(
    ! [C_21,A_22,B_23] :
      ( v1_funct_2(C_21,A_22,B_23)
      | ~ r2_hidden(C_21,k1_funct_2(A_22,B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_61,plain,(
    ! [A_41,A_42,B_43] :
      ( v1_funct_2(A_41,A_42,B_43)
      | v1_xboole_0(k1_funct_2(A_42,B_43))
      | ~ m1_subset_1(A_41,k1_funct_2(A_42,B_43)) ) ),
    inference(resolution,[status(thm)],[c_20,c_33])).

tff(c_66,plain,(
    ! [A_1,B_2,A_42,B_43] :
      ( v1_funct_2('#skF_1'(A_1,B_2,k1_funct_2(A_42,B_43)),A_42,B_43)
      | m1_funct_2(k1_funct_2(A_42,B_43),A_1,B_2)
      | v1_xboole_0(k1_funct_2(A_42,B_43)) ) ),
    inference(resolution,[status(thm)],[c_4,c_61])).

tff(c_14,plain,(
    ! [C_11,A_9,B_10] :
      ( m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ r2_hidden(C_11,k1_funct_2(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76,plain,(
    ! [A_58,B_59,C_60] :
      ( ~ m1_subset_1('#skF_1'(A_58,B_59,C_60),k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ v1_funct_2('#skF_1'(A_58,B_59,C_60),A_58,B_59)
      | ~ v1_funct_1('#skF_1'(A_58,B_59,C_60))
      | m1_funct_2(C_60,A_58,B_59)
      | v1_xboole_0(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_106,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ v1_funct_2('#skF_1'(A_84,B_85,C_86),A_84,B_85)
      | ~ v1_funct_1('#skF_1'(A_84,B_85,C_86))
      | m1_funct_2(C_86,A_84,B_85)
      | v1_xboole_0(C_86)
      | ~ r2_hidden('#skF_1'(A_84,B_85,C_86),k1_funct_2(A_84,B_85)) ) ),
    inference(resolution,[status(thm)],[c_14,c_76])).

tff(c_118,plain,(
    ! [A_96,B_97,C_98] :
      ( ~ v1_funct_2('#skF_1'(A_96,B_97,C_98),A_96,B_97)
      | ~ v1_funct_1('#skF_1'(A_96,B_97,C_98))
      | m1_funct_2(C_98,A_96,B_97)
      | v1_xboole_0(C_98)
      | v1_xboole_0(k1_funct_2(A_96,B_97))
      | ~ m1_subset_1('#skF_1'(A_96,B_97,C_98),k1_funct_2(A_96,B_97)) ) ),
    inference(resolution,[status(thm)],[c_20,c_106])).

tff(c_125,plain,(
    ! [A_106,B_107] :
      ( ~ v1_funct_2('#skF_1'(A_106,B_107,k1_funct_2(A_106,B_107)),A_106,B_107)
      | ~ v1_funct_1('#skF_1'(A_106,B_107,k1_funct_2(A_106,B_107)))
      | m1_funct_2(k1_funct_2(A_106,B_107),A_106,B_107)
      | v1_xboole_0(k1_funct_2(A_106,B_107)) ) ),
    inference(resolution,[status(thm)],[c_4,c_118])).

tff(c_136,plain,(
    ! [A_108,B_109] :
      ( ~ v1_funct_1('#skF_1'(A_108,B_109,k1_funct_2(A_108,B_109)))
      | m1_funct_2(k1_funct_2(A_108,B_109),A_108,B_109)
      | v1_xboole_0(k1_funct_2(A_108,B_109)) ) ),
    inference(resolution,[status(thm)],[c_66,c_125])).

tff(c_142,plain,(
    ! [A_110,B_111] :
      ( m1_funct_2(k1_funct_2(A_110,B_111),A_110,B_111)
      | v1_xboole_0(k1_funct_2(A_110,B_111)) ) ),
    inference(resolution,[status(thm)],[c_52,c_136])).

tff(c_22,plain,(
    ~ m1_funct_2(k1_funct_2('#skF_2','#skF_3'),'#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_149,plain,(
    v1_xboole_0(k1_funct_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_142,c_22])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( ~ v1_xboole_0(k1_funct_2(A_7,B_8))
      | v1_xboole_0(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_152,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_149,c_12])).

tff(c_156,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_152])).

%------------------------------------------------------------------------------
