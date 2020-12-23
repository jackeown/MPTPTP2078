%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1051+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:19 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 119 expanded)
%              Number of leaves         :   22 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :  103 ( 363 expanded)
%              Number of equality atoms :   14 (  76 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r1_relset_1 > r1_tarski > m1_subset_1 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_relset_1,type,(
    r1_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ( ! [E] : B != k1_tarski(E)
                & k5_partfun1(A,B,C) = k5_partfun1(A,B,D) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_2)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( r1_tarski(k5_partfun1(A,B,C),k5_partfun1(A,B,D))
              & ! [E] : B != k1_tarski(E) )
           => r1_relset_1(A,B,D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_2)).

tff(f_36,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_relset_1(A,B,C,D)
      <=> r1_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_63,plain,(
    ! [A_38,B_39,C_40,D_41] :
      ( r2_relset_1(A_38,B_39,C_40,C_40)
      | ~ m1_subset_1(D_41,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39)))
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_70,plain,(
    ! [C_42] :
      ( r2_relset_1('#skF_2','#skF_3',C_42,C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_26,c_63])).

tff(c_75,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_70])).

tff(c_28,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_20,plain,(
    ! [E_23] : k1_tarski(E_23) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_18,plain,(
    k5_partfun1('#skF_2','#skF_3','#skF_5') = k5_partfun1('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_77,plain,(
    ! [A_43,B_44,D_45,C_46] :
      ( r1_relset_1(A_43,B_44,D_45,C_46)
      | k1_tarski('#skF_1'(A_43,B_44,C_46,D_45)) = B_44
      | ~ r1_tarski(k5_partfun1(A_43,B_44,C_46),k5_partfun1(A_43,B_44,D_45))
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ v1_funct_1(D_45)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44)))
      | ~ v1_funct_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_80,plain,(
    ! [D_45] :
      ( r1_relset_1('#skF_2','#skF_3',D_45,'#skF_5')
      | k1_tarski('#skF_1'('#skF_2','#skF_3','#skF_5',D_45)) = '#skF_3'
      | ~ r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),k5_partfun1('#skF_2','#skF_3',D_45))
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(D_45)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_77])).

tff(c_89,plain,(
    ! [D_45] :
      ( r1_relset_1('#skF_2','#skF_3',D_45,'#skF_5')
      | k1_tarski('#skF_1'('#skF_2','#skF_3','#skF_5',D_45)) = '#skF_3'
      | ~ r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),k5_partfun1('#skF_2','#skF_3',D_45))
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(D_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_80])).

tff(c_95,plain,(
    ! [D_47] :
      ( r1_relset_1('#skF_2','#skF_3',D_47,'#skF_5')
      | ~ r1_tarski(k5_partfun1('#skF_2','#skF_3','#skF_4'),k5_partfun1('#skF_2','#skF_3',D_47))
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(D_47) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_89])).

tff(c_102,plain,
    ( r1_relset_1('#skF_2','#skF_3','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_95])).

tff(c_107,plain,(
    r1_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_102])).

tff(c_10,plain,(
    ! [C_5,D_6,A_3,B_4] :
      ( r1_tarski(C_5,D_6)
      | ~ r1_relset_1(A_3,B_4,C_5,D_6)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_114,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_107,c_10])).

tff(c_117,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_114])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_120,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_117,c_2])).

tff(c_121,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_83,plain,(
    ! [C_46] :
      ( r1_relset_1('#skF_2','#skF_3','#skF_5',C_46)
      | k1_tarski('#skF_1'('#skF_2','#skF_3',C_46,'#skF_5')) = '#skF_3'
      | ~ r1_tarski(k5_partfun1('#skF_2','#skF_3',C_46),k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_77])).

tff(c_92,plain,(
    ! [C_46] :
      ( r1_relset_1('#skF_2','#skF_3','#skF_5',C_46)
      | k1_tarski('#skF_1'('#skF_2','#skF_3',C_46,'#skF_5')) = '#skF_3'
      | ~ r1_tarski(k5_partfun1('#skF_2','#skF_3',C_46),k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_83])).

tff(c_140,plain,(
    ! [C_51] :
      ( r1_relset_1('#skF_2','#skF_3','#skF_5',C_51)
      | ~ r1_tarski(k5_partfun1('#skF_2','#skF_3',C_51),k5_partfun1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1(C_51) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_92])).

tff(c_147,plain,
    ( r1_relset_1('#skF_2','#skF_3','#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_140])).

tff(c_152,plain,(
    r1_relset_1('#skF_2','#skF_3','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_147])).

tff(c_154,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_152,c_10])).

tff(c_157,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_154])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_157])).

tff(c_160,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_16,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_184,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_16])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_184])).

%------------------------------------------------------------------------------
