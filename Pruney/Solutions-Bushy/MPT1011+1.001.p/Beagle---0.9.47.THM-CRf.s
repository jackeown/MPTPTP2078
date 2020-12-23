%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1011+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:14 EST 2020

% Result     : Theorem 1.46s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 100 expanded)
%              Number of leaves         :   20 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :   90 ( 351 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,k1_tarski(B))
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,k1_tarski(B))
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
           => r2_relset_1(A,k1_tarski(B),C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,A,B)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ! [E] :
                ( r2_hidden(E,A)
               => k1_funct_1(C,E) = k1_funct_1(D,E) )
           => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,k1_tarski(B))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
     => ( r2_hidden(C,A)
       => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(c_8,plain,(
    ~ r2_relset_1('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    v1_funct_2('#skF_4','#skF_2',k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_tarski('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,(
    v1_funct_2('#skF_5','#skF_2',k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_10,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_tarski('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    ! [A_18,B_19,C_20,D_21] :
      ( r2_hidden('#skF_1'(A_18,B_19,C_20,D_21),A_18)
      | r2_relset_1(A_18,B_19,C_20,D_21)
      | ~ m1_subset_1(D_21,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_2(D_21,A_18,B_19)
      | ~ v1_funct_1(D_21)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_2(C_20,A_18,B_19)
      | ~ v1_funct_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    ! [C_20] :
      ( r2_hidden('#skF_1'('#skF_2',k1_tarski('#skF_3'),C_20,'#skF_5'),'#skF_2')
      | r2_relset_1('#skF_2',k1_tarski('#skF_3'),C_20,'#skF_5')
      | ~ v1_funct_2('#skF_5','#skF_2',k1_tarski('#skF_3'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_tarski('#skF_3'))))
      | ~ v1_funct_2(C_20,'#skF_2',k1_tarski('#skF_3'))
      | ~ v1_funct_1(C_20) ) ),
    inference(resolution,[status(thm)],[c_10,c_22])).

tff(c_48,plain,(
    ! [C_23] :
      ( r2_hidden('#skF_1'('#skF_2',k1_tarski('#skF_3'),C_23,'#skF_5'),'#skF_2')
      | r2_relset_1('#skF_2',k1_tarski('#skF_3'),C_23,'#skF_5')
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_tarski('#skF_3'))))
      | ~ v1_funct_2(C_23,'#skF_2',k1_tarski('#skF_3'))
      | ~ v1_funct_1(C_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_26])).

tff(c_51,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5'),'#skF_2')
    | r2_relset_1('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_4','#skF_2',k1_tarski('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_48])).

tff(c_57,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5'),'#skF_2')
    | r2_relset_1('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_51])).

tff(c_58,plain,(
    r2_hidden('#skF_1'('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_57])).

tff(c_6,plain,(
    ! [D_12,C_11,B_10,A_9] :
      ( k1_funct_1(D_12,C_11) = B_10
      | ~ r2_hidden(C_11,A_9)
      | ~ m1_subset_1(D_12,k1_zfmisc_1(k2_zfmisc_1(A_9,k1_tarski(B_10))))
      | ~ v1_funct_2(D_12,A_9,k1_tarski(B_10))
      | ~ v1_funct_1(D_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_70,plain,(
    ! [D_28,B_29] :
      ( k1_funct_1(D_28,'#skF_1'('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5')) = B_29
      | ~ m1_subset_1(D_28,k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_tarski(B_29))))
      | ~ v1_funct_2(D_28,'#skF_2',k1_tarski(B_29))
      | ~ v1_funct_1(D_28) ) ),
    inference(resolution,[status(thm)],[c_58,c_6])).

tff(c_73,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5')) = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_2',k1_tarski('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_70])).

tff(c_79,plain,(
    k1_funct_1('#skF_4','#skF_1'('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_73])).

tff(c_76,plain,
    ( k1_funct_1('#skF_5','#skF_1'('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5')) = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_2',k1_tarski('#skF_3'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_70])).

tff(c_82,plain,(
    k1_funct_1('#skF_5','#skF_1'('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_12,c_76])).

tff(c_2,plain,(
    ! [D_7,A_1,B_2,C_3] :
      ( k1_funct_1(D_7,'#skF_1'(A_1,B_2,C_3,D_7)) != k1_funct_1(C_3,'#skF_1'(A_1,B_2,C_3,D_7))
      | r2_relset_1(A_1,B_2,C_3,D_7)
      | ~ m1_subset_1(D_7,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_7,A_1,B_2)
      | ~ v1_funct_1(D_7)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_89,plain,
    ( k1_funct_1('#skF_4','#skF_1'('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5')) != '#skF_3'
    | r2_relset_1('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_tarski('#skF_3'))))
    | ~ v1_funct_2('#skF_5','#skF_2',k1_tarski('#skF_3'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_tarski('#skF_3'))))
    | ~ v1_funct_2('#skF_4','#skF_2',k1_tarski('#skF_3'))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_2])).

tff(c_93,plain,(
    r2_relset_1('#skF_2',k1_tarski('#skF_3'),'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_14,c_12,c_10,c_79,c_89])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_93])).

%------------------------------------------------------------------------------
