%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1030+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:17 EST 2020

% Result     : Theorem 1.49s
% Output     : CNFRefutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 155 expanded)
%              Number of leaves         :   20 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :   91 ( 380 expanded)
%              Number of equality atoms :   21 ( 142 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k3_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => v1_partfun1(k3_partfun1(C,A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_funct_2)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k3_partfun1(C,A,B) = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_partfun1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(c_14,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_21,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_20,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_29,plain,(
    ! [C_17,A_18,B_19] :
      ( k3_partfun1(C_17,A_18,B_19) = C_17
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_2') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_29])).

tff(c_35,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_32])).

tff(c_12,plain,(
    ~ v1_partfun1(k3_partfun1('#skF_3','#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_12])).

tff(c_18,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_41,plain,(
    ! [C_20,A_21,B_22] :
      ( v1_partfun1(C_20,A_21)
      | ~ v1_funct_2(C_20,A_21,B_22)
      | ~ v1_funct_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | v1_xboole_0(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_44,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_41])).

tff(c_47,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_44])).

tff(c_48,plain,(
    v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_47])).

tff(c_8,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_51,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_48,c_8])).

tff(c_55,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21,c_51])).

tff(c_56,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_57,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_62,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_57])).

tff(c_71,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_16])).

tff(c_72,plain,(
    ! [C_24,A_25,B_26] :
      ( v1_partfun1(C_24,A_25)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26)))
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_71,c_72])).

tff(c_77,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_63,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_18])).

tff(c_85,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_partfun1(C_30,A_31)
      | ~ v1_funct_2(C_30,A_31,B_32)
      | ~ v1_funct_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | v1_xboole_0(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_88,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_71,c_85])).

tff(c_91,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_63,c_88])).

tff(c_92,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_91])).

tff(c_78,plain,(
    ! [C_27,A_28,B_29] :
      ( k3_partfun1(C_27,A_28,B_29) = C_27
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_81,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_78])).

tff(c_84,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_81])).

tff(c_70,plain,(
    ~ v1_partfun1(k3_partfun1('#skF_3','#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_12])).

tff(c_93,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_70])).

tff(c_96,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_93])).

tff(c_97,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_104,plain,(
    ! [C_33,A_34,B_35] :
      ( k3_partfun1(C_33,A_34,B_35) = C_33
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_107,plain,
    ( k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_71,c_104])).

tff(c_110,plain,(
    k3_partfun1('#skF_3','#skF_1','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_107])).

tff(c_111,plain,(
    ~ v1_partfun1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_70])).

tff(c_114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_111])).

%------------------------------------------------------------------------------
