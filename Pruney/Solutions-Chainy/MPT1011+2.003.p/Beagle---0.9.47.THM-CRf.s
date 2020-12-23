%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:33 EST 2020

% Result     : Theorem 9.81s
% Output     : CNFRefutation 9.81s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 172 expanded)
%              Number of leaves         :   29 (  77 expanded)
%              Depth                    :   15
%              Number of atoms          :  152 ( 607 expanded)
%              Number of equality atoms :   43 ( 108 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_88,negated_conjecture,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_40,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_60,axiom,(
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

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_34,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32,plain,(
    v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_14,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_105,plain,(
    ! [D_42,C_43,B_44,A_45] :
      ( r2_hidden(k1_funct_1(D_42,C_43),B_44)
      | k1_xboole_0 = B_44
      | ~ r2_hidden(C_43,A_45)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_45,B_44)))
      | ~ v1_funct_2(D_42,A_45,B_44)
      | ~ v1_funct_1(D_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_116,plain,(
    ! [D_49,A_50,B_51,B_52] :
      ( r2_hidden(k1_funct_1(D_49,'#skF_2'(A_50,B_51)),B_52)
      | k1_xboole_0 = B_52
      | ~ m1_subset_1(D_49,k1_zfmisc_1(k2_zfmisc_1(B_51,B_52)))
      | ~ v1_funct_2(D_49,B_51,B_52)
      | ~ v1_funct_1(D_49)
      | '#skF_1'(A_50,B_51) = A_50
      | k1_tarski(A_50) = B_51 ) ),
    inference(resolution,[status(thm)],[c_14,c_105])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_129,plain,(
    ! [D_57,A_58,B_59,A_60] :
      ( k1_funct_1(D_57,'#skF_2'(A_58,B_59)) = A_60
      | k1_tarski(A_60) = k1_xboole_0
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(B_59,k1_tarski(A_60))))
      | ~ v1_funct_2(D_57,B_59,k1_tarski(A_60))
      | ~ v1_funct_1(D_57)
      | '#skF_1'(A_58,B_59) = A_58
      | k1_tarski(A_58) = B_59 ) ),
    inference(resolution,[status(thm)],[c_116,c_4])).

tff(c_131,plain,(
    ! [A_58] :
      ( k1_funct_1('#skF_7','#skF_2'(A_58,'#skF_4')) = '#skF_5'
      | k1_tarski('#skF_5') = k1_xboole_0
      | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5'))
      | ~ v1_funct_1('#skF_7')
      | '#skF_1'(A_58,'#skF_4') = A_58
      | k1_tarski(A_58) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_30,c_129])).

tff(c_136,plain,(
    ! [A_58] :
      ( k1_funct_1('#skF_7','#skF_2'(A_58,'#skF_4')) = '#skF_5'
      | k1_tarski('#skF_5') = k1_xboole_0
      | '#skF_1'(A_58,'#skF_4') = A_58
      | k1_tarski(A_58) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_131])).

tff(c_140,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_20,plain,(
    ! [A_9] : ~ v1_xboole_0(k1_tarski(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_179,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_20])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_179])).

tff(c_191,plain,(
    k1_tarski('#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_38,plain,(
    v1_funct_2('#skF_6','#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    ~ r2_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_276,plain,(
    ! [A_68,B_69,C_70,D_71] :
      ( r2_hidden('#skF_3'(A_68,B_69,C_70,D_71),A_68)
      | r2_relset_1(A_68,B_69,C_70,D_71)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ v1_funct_2(D_71,A_68,B_69)
      | ~ v1_funct_1(D_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ v1_funct_2(C_70,A_68,B_69)
      | ~ v1_funct_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_278,plain,(
    ! [C_70] :
      ( r2_hidden('#skF_3'('#skF_4',k1_tarski('#skF_5'),C_70,'#skF_7'),'#skF_4')
      | r2_relset_1('#skF_4',k1_tarski('#skF_5'),C_70,'#skF_7')
      | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5'))))
      | ~ v1_funct_2(C_70,'#skF_4',k1_tarski('#skF_5'))
      | ~ v1_funct_1(C_70) ) ),
    inference(resolution,[status(thm)],[c_30,c_276])).

tff(c_5014,plain,(
    ! [C_1567] :
      ( r2_hidden('#skF_3'('#skF_4',k1_tarski('#skF_5'),C_1567,'#skF_7'),'#skF_4')
      | r2_relset_1('#skF_4',k1_tarski('#skF_5'),C_1567,'#skF_7')
      | ~ m1_subset_1(C_1567,k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5'))))
      | ~ v1_funct_2(C_1567,'#skF_4',k1_tarski('#skF_5'))
      | ~ v1_funct_1(C_1567) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_278])).

tff(c_5325,plain,
    ( r2_hidden('#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7'),'#skF_4')
    | r2_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')
    | ~ v1_funct_2('#skF_6','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_5014])).

tff(c_5334,plain,
    ( r2_hidden('#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7'),'#skF_4')
    | r2_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_5325])).

tff(c_5335,plain,(
    r2_hidden('#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_5334])).

tff(c_26,plain,(
    ! [D_21,C_20,B_19,A_18] :
      ( r2_hidden(k1_funct_1(D_21,C_20),B_19)
      | k1_xboole_0 = B_19
      | ~ r2_hidden(C_20,A_18)
      | ~ m1_subset_1(D_21,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_2(D_21,A_18,B_19)
      | ~ v1_funct_1(D_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_9603,plain,(
    ! [D_3557,B_3558] :
      ( r2_hidden(k1_funct_1(D_3557,'#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')),B_3558)
      | k1_xboole_0 = B_3558
      | ~ m1_subset_1(D_3557,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_3558)))
      | ~ v1_funct_2(D_3557,'#skF_4',B_3558)
      | ~ v1_funct_1(D_3557) ) ),
    inference(resolution,[status(thm)],[c_5335,c_26])).

tff(c_27429,plain,(
    ! [D_7759,A_7760] :
      ( k1_funct_1(D_7759,'#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) = A_7760
      | k1_tarski(A_7760) = k1_xboole_0
      | ~ m1_subset_1(D_7759,k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski(A_7760))))
      | ~ v1_funct_2(D_7759,'#skF_4',k1_tarski(A_7760))
      | ~ v1_funct_1(D_7759) ) ),
    inference(resolution,[status(thm)],[c_9603,c_4])).

tff(c_28001,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) = '#skF_5'
    | k1_tarski('#skF_5') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_27429])).

tff(c_28008,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) = '#skF_5'
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_28001])).

tff(c_28009,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_28008])).

tff(c_27998,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) = '#skF_5'
    | k1_tarski('#skF_5') = k1_xboole_0
    | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_27429])).

tff(c_28004,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) = '#skF_5'
    | k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_27998])).

tff(c_28005,plain,(
    k1_funct_1('#skF_7','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_28004])).

tff(c_22,plain,(
    ! [D_16,A_10,B_11,C_12] :
      ( k1_funct_1(D_16,'#skF_3'(A_10,B_11,C_12,D_16)) != k1_funct_1(C_12,'#skF_3'(A_10,B_11,C_12,D_16))
      | r2_relset_1(A_10,B_11,C_12,D_16)
      | ~ m1_subset_1(D_16,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_2(D_16,A_10,B_11)
      | ~ v1_funct_1(D_16)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11)))
      | ~ v1_funct_2(C_12,A_10,B_11)
      | ~ v1_funct_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28021,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) != '#skF_5'
    | r2_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5'))))
    | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5'))))
    | ~ v1_funct_2('#skF_6','#skF_4',k1_tarski('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_28005,c_22])).

tff(c_28923,plain,
    ( k1_funct_1('#skF_6','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) != '#skF_5'
    | r2_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_34,c_32,c_30,c_28021])).

tff(c_28924,plain,(
    k1_funct_1('#skF_6','#skF_3'('#skF_4',k1_tarski('#skF_5'),'#skF_6','#skF_7')) != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28923])).

tff(c_30048,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28009,c_28924])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:11:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.81/3.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.81/3.31  
% 9.81/3.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.81/3.32  %$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3 > #skF_1
% 9.81/3.32  
% 9.81/3.32  %Foreground sorts:
% 9.81/3.32  
% 9.81/3.32  
% 9.81/3.32  %Background operators:
% 9.81/3.32  
% 9.81/3.32  
% 9.81/3.32  %Foreground operators:
% 9.81/3.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.81/3.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.81/3.32  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.81/3.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.81/3.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.81/3.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.81/3.32  tff('#skF_7', type, '#skF_7': $i).
% 9.81/3.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.81/3.32  tff('#skF_5', type, '#skF_5': $i).
% 9.81/3.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.81/3.32  tff('#skF_6', type, '#skF_6': $i).
% 9.81/3.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.81/3.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.81/3.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.81/3.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.81/3.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.81/3.32  tff('#skF_4', type, '#skF_4': $i).
% 9.81/3.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.81/3.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.81/3.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 9.81/3.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.81/3.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.81/3.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.81/3.32  
% 9.81/3.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.81/3.33  tff(f_88, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, k1_tarski(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => r2_relset_1(A, k1_tarski(B), C, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_funct_2)).
% 9.81/3.33  tff(f_33, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 9.81/3.33  tff(f_72, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 9.81/3.33  tff(f_40, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 9.81/3.33  tff(f_60, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 9.81/3.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.81/3.33  tff(c_34, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.81/3.33  tff(c_32, plain, (v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.81/3.33  tff(c_30, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.81/3.33  tff(c_14, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.81/3.33  tff(c_105, plain, (![D_42, C_43, B_44, A_45]: (r2_hidden(k1_funct_1(D_42, C_43), B_44) | k1_xboole_0=B_44 | ~r2_hidden(C_43, A_45) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(A_45, B_44))) | ~v1_funct_2(D_42, A_45, B_44) | ~v1_funct_1(D_42))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.81/3.33  tff(c_116, plain, (![D_49, A_50, B_51, B_52]: (r2_hidden(k1_funct_1(D_49, '#skF_2'(A_50, B_51)), B_52) | k1_xboole_0=B_52 | ~m1_subset_1(D_49, k1_zfmisc_1(k2_zfmisc_1(B_51, B_52))) | ~v1_funct_2(D_49, B_51, B_52) | ~v1_funct_1(D_49) | '#skF_1'(A_50, B_51)=A_50 | k1_tarski(A_50)=B_51)), inference(resolution, [status(thm)], [c_14, c_105])).
% 9.81/3.33  tff(c_4, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.81/3.33  tff(c_129, plain, (![D_57, A_58, B_59, A_60]: (k1_funct_1(D_57, '#skF_2'(A_58, B_59))=A_60 | k1_tarski(A_60)=k1_xboole_0 | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(B_59, k1_tarski(A_60)))) | ~v1_funct_2(D_57, B_59, k1_tarski(A_60)) | ~v1_funct_1(D_57) | '#skF_1'(A_58, B_59)=A_58 | k1_tarski(A_58)=B_59)), inference(resolution, [status(thm)], [c_116, c_4])).
% 9.81/3.33  tff(c_131, plain, (![A_58]: (k1_funct_1('#skF_7', '#skF_2'(A_58, '#skF_4'))='#skF_5' | k1_tarski('#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_7') | '#skF_1'(A_58, '#skF_4')=A_58 | k1_tarski(A_58)='#skF_4')), inference(resolution, [status(thm)], [c_30, c_129])).
% 9.81/3.33  tff(c_136, plain, (![A_58]: (k1_funct_1('#skF_7', '#skF_2'(A_58, '#skF_4'))='#skF_5' | k1_tarski('#skF_5')=k1_xboole_0 | '#skF_1'(A_58, '#skF_4')=A_58 | k1_tarski(A_58)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_131])).
% 9.81/3.33  tff(c_140, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_136])).
% 9.81/3.33  tff(c_20, plain, (![A_9]: (~v1_xboole_0(k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.81/3.33  tff(c_179, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_140, c_20])).
% 9.81/3.33  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_179])).
% 9.81/3.33  tff(c_191, plain, (k1_tarski('#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_136])).
% 9.81/3.33  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.81/3.33  tff(c_38, plain, (v1_funct_2('#skF_6', '#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.81/3.33  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.81/3.33  tff(c_28, plain, (~r2_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.81/3.33  tff(c_276, plain, (![A_68, B_69, C_70, D_71]: (r2_hidden('#skF_3'(A_68, B_69, C_70, D_71), A_68) | r2_relset_1(A_68, B_69, C_70, D_71) | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~v1_funct_2(D_71, A_68, B_69) | ~v1_funct_1(D_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~v1_funct_2(C_70, A_68, B_69) | ~v1_funct_1(C_70))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.81/3.33  tff(c_278, plain, (![C_70]: (r2_hidden('#skF_3'('#skF_4', k1_tarski('#skF_5'), C_70, '#skF_7'), '#skF_4') | r2_relset_1('#skF_4', k1_tarski('#skF_5'), C_70, '#skF_7') | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_7') | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5')))) | ~v1_funct_2(C_70, '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1(C_70))), inference(resolution, [status(thm)], [c_30, c_276])).
% 9.81/3.33  tff(c_5014, plain, (![C_1567]: (r2_hidden('#skF_3'('#skF_4', k1_tarski('#skF_5'), C_1567, '#skF_7'), '#skF_4') | r2_relset_1('#skF_4', k1_tarski('#skF_5'), C_1567, '#skF_7') | ~m1_subset_1(C_1567, k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5')))) | ~v1_funct_2(C_1567, '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1(C_1567))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_278])).
% 9.81/3.33  tff(c_5325, plain, (r2_hidden('#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'), '#skF_4') | r2_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7') | ~v1_funct_2('#skF_6', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_5014])).
% 9.81/3.33  tff(c_5334, plain, (r2_hidden('#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'), '#skF_4') | r2_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_5325])).
% 9.81/3.33  tff(c_5335, plain, (r2_hidden('#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_28, c_5334])).
% 9.81/3.33  tff(c_26, plain, (![D_21, C_20, B_19, A_18]: (r2_hidden(k1_funct_1(D_21, C_20), B_19) | k1_xboole_0=B_19 | ~r2_hidden(C_20, A_18) | ~m1_subset_1(D_21, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~v1_funct_2(D_21, A_18, B_19) | ~v1_funct_1(D_21))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.81/3.33  tff(c_9603, plain, (![D_3557, B_3558]: (r2_hidden(k1_funct_1(D_3557, '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7')), B_3558) | k1_xboole_0=B_3558 | ~m1_subset_1(D_3557, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_3558))) | ~v1_funct_2(D_3557, '#skF_4', B_3558) | ~v1_funct_1(D_3557))), inference(resolution, [status(thm)], [c_5335, c_26])).
% 9.81/3.33  tff(c_27429, plain, (![D_7759, A_7760]: (k1_funct_1(D_7759, '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))=A_7760 | k1_tarski(A_7760)=k1_xboole_0 | ~m1_subset_1(D_7759, k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski(A_7760)))) | ~v1_funct_2(D_7759, '#skF_4', k1_tarski(A_7760)) | ~v1_funct_1(D_7759))), inference(resolution, [status(thm)], [c_9603, c_4])).
% 9.81/3.33  tff(c_28001, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))='#skF_5' | k1_tarski('#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_27429])).
% 9.81/3.33  tff(c_28008, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))='#skF_5' | k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_28001])).
% 9.81/3.33  tff(c_28009, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_191, c_28008])).
% 9.81/3.33  tff(c_27998, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))='#skF_5' | k1_tarski('#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_30, c_27429])).
% 9.81/3.33  tff(c_28004, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))='#skF_5' | k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_27998])).
% 9.81/3.33  tff(c_28005, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_191, c_28004])).
% 9.81/3.33  tff(c_22, plain, (![D_16, A_10, B_11, C_12]: (k1_funct_1(D_16, '#skF_3'(A_10, B_11, C_12, D_16))!=k1_funct_1(C_12, '#skF_3'(A_10, B_11, C_12, D_16)) | r2_relset_1(A_10, B_11, C_12, D_16) | ~m1_subset_1(D_16, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))) | ~v1_funct_2(D_16, A_10, B_11) | ~v1_funct_1(D_16) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))) | ~v1_funct_2(C_12, A_10, B_11) | ~v1_funct_1(C_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.81/3.33  tff(c_28021, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))!='#skF_5' | r2_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5')))) | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5')))) | ~v1_funct_2('#skF_6', '#skF_4', k1_tarski('#skF_5')) | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_28005, c_22])).
% 9.81/3.33  tff(c_28923, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))!='#skF_5' | r2_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_34, c_32, c_30, c_28021])).
% 9.81/3.33  tff(c_28924, plain, (k1_funct_1('#skF_6', '#skF_3'('#skF_4', k1_tarski('#skF_5'), '#skF_6', '#skF_7'))!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_28, c_28923])).
% 9.81/3.33  tff(c_30048, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28009, c_28924])).
% 9.81/3.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.81/3.33  
% 9.81/3.33  Inference rules
% 9.81/3.33  ----------------------
% 9.81/3.33  #Ref     : 1
% 9.81/3.33  #Sup     : 2129
% 9.81/3.33  #Fact    : 4
% 9.81/3.33  #Define  : 0
% 9.81/3.33  #Split   : 32
% 9.81/3.33  #Chain   : 0
% 9.81/3.33  #Close   : 0
% 9.81/3.33  
% 9.81/3.33  Ordering : KBO
% 9.81/3.33  
% 9.81/3.33  Simplification rules
% 9.81/3.33  ----------------------
% 9.81/3.33  #Subsume      : 256
% 9.81/3.33  #Demod        : 654
% 9.81/3.33  #Tautology    : 387
% 9.81/3.33  #SimpNegUnit  : 10
% 9.81/3.33  #BackRed      : 6
% 9.81/3.33  
% 9.81/3.33  #Partial instantiations: 5880
% 9.81/3.33  #Strategies tried      : 1
% 9.81/3.33  
% 9.81/3.33  Timing (in seconds)
% 9.81/3.33  ----------------------
% 9.81/3.33  Preprocessing        : 0.29
% 9.81/3.33  Parsing              : 0.15
% 9.81/3.33  CNF conversion       : 0.02
% 9.81/3.33  Main loop            : 2.22
% 9.81/3.33  Inferencing          : 0.83
% 9.81/3.33  Reduction            : 0.51
% 9.81/3.33  Demodulation         : 0.36
% 9.81/3.33  BG Simplification    : 0.10
% 9.81/3.33  Subsumption          : 0.67
% 9.81/3.33  Abstraction          : 0.14
% 9.81/3.33  MUC search           : 0.00
% 9.81/3.33  Cooper               : 0.00
% 9.81/3.33  Total                : 2.54
% 9.81/3.33  Index Insertion      : 0.00
% 9.81/3.33  Index Deletion       : 0.00
% 9.81/3.33  Index Matching       : 0.00
% 9.81/3.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
