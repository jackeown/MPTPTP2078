%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:42 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 120 expanded)
%              Number of leaves         :   31 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  123 ( 387 expanded)
%              Number of equality atoms :   47 ( 144 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,B,D) = B
                & k2_relset_1(B,C,E) = C )
             => ( C = k1_xboole_0
                | k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_46,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_285,plain,(
    ! [B_75,C_74,E_76,D_79,A_78,F_77] :
      ( k1_partfun1(A_78,B_75,C_74,D_79,E_76,F_77) = k5_relat_1(E_76,F_77)
      | ~ m1_subset_1(F_77,k1_zfmisc_1(k2_zfmisc_1(C_74,D_79)))
      | ~ v1_funct_1(F_77)
      | ~ m1_subset_1(E_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_75)))
      | ~ v1_funct_1(E_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_287,plain,(
    ! [A_78,B_75,E_76] :
      ( k1_partfun1(A_78,B_75,'#skF_2','#skF_3',E_76,'#skF_5') = k5_relat_1(E_76,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_76,k1_zfmisc_1(k2_zfmisc_1(A_78,B_75)))
      | ~ v1_funct_1(E_76) ) ),
    inference(resolution,[status(thm)],[c_42,c_285])).

tff(c_296,plain,(
    ! [A_80,B_81,E_82] :
      ( k1_partfun1(A_80,B_81,'#skF_2','#skF_3',E_82,'#skF_5') = k5_relat_1(E_82,'#skF_5')
      | ~ m1_subset_1(E_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81)))
      | ~ v1_funct_1(E_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_287])).

tff(c_302,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_296])).

tff(c_308,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_302])).

tff(c_34,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_427,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_34])).

tff(c_70,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_77,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_70])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_79,plain,(
    ! [A_37,B_38,C_39] :
      ( k2_relset_1(A_37,B_38,C_39) = k2_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_82,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_79])).

tff(c_87,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_82])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_44,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_99,plain,(
    ! [A_41,B_42,C_43] :
      ( k1_relset_1(A_41,B_42,C_43) = k1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_106,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_99])).

tff(c_132,plain,(
    ! [B_54,A_55,C_56] :
      ( k1_xboole_0 = B_54
      | k1_relset_1(A_55,B_54,C_56) = A_55
      | ~ v1_funct_2(C_56,A_55,B_54)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_55,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_135,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_132])).

tff(c_141,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_106,c_135])).

tff(c_142,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_141])).

tff(c_78,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_70])).

tff(c_40,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_85,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_79])).

tff(c_89,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_85])).

tff(c_119,plain,(
    ! [B_50,A_51] :
      ( k2_relat_1(k5_relat_1(B_50,A_51)) = k2_relat_1(A_51)
      | ~ r1_tarski(k1_relat_1(A_51),k2_relat_1(B_50))
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_122,plain,(
    ! [A_51] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_51)) = k2_relat_1(A_51)
      | ~ r1_tarski(k1_relat_1(A_51),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_119])).

tff(c_127,plain,(
    ! [A_51] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_51)) = k2_relat_1(A_51)
      | ~ r1_tarski(k1_relat_1(A_51),'#skF_2')
      | ~ v1_relat_1(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_122])).

tff(c_153,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_127])).

tff(c_162,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_6,c_87,c_153])).

tff(c_28,plain,(
    ! [E_22,D_21,F_23,A_18,C_20,B_19] :
      ( m1_subset_1(k1_partfun1(A_18,B_19,C_20,D_21,E_22,F_23),k1_zfmisc_1(k2_zfmisc_1(A_18,D_21)))
      | ~ m1_subset_1(F_23,k1_zfmisc_1(k2_zfmisc_1(C_20,D_21)))
      | ~ v1_funct_1(F_23)
      | ~ m1_subset_1(E_22,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19)))
      | ~ v1_funct_1(E_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_431,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_28])).

tff(c_435,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_46,c_42,c_431])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] :
      ( k2_relset_1(A_12,B_13,C_14) = k2_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_487,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_435,c_14])).

tff(c_517,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_487])).

tff(c_519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_517])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:15:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.40  
% 2.73/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.40  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.73/1.40  
% 2.73/1.40  %Foreground sorts:
% 2.73/1.40  
% 2.73/1.40  
% 2.73/1.40  %Background operators:
% 2.73/1.40  
% 2.73/1.40  
% 2.73/1.40  %Foreground operators:
% 2.73/1.40  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.73/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.40  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.73/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.73/1.40  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.73/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.73/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.73/1.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.73/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.40  
% 2.73/1.42  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_funct_2)).
% 2.73/1.42  tff(f_92, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.73/1.42  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.73/1.42  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.73/1.42  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.73/1.42  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.73/1.42  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.73/1.42  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 2.73/1.42  tff(f_82, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 2.73/1.42  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.73/1.42  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.73/1.42  tff(c_46, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.73/1.42  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.73/1.42  tff(c_285, plain, (![B_75, C_74, E_76, D_79, A_78, F_77]: (k1_partfun1(A_78, B_75, C_74, D_79, E_76, F_77)=k5_relat_1(E_76, F_77) | ~m1_subset_1(F_77, k1_zfmisc_1(k2_zfmisc_1(C_74, D_79))) | ~v1_funct_1(F_77) | ~m1_subset_1(E_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_75))) | ~v1_funct_1(E_76))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.73/1.42  tff(c_287, plain, (![A_78, B_75, E_76]: (k1_partfun1(A_78, B_75, '#skF_2', '#skF_3', E_76, '#skF_5')=k5_relat_1(E_76, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_76, k1_zfmisc_1(k2_zfmisc_1(A_78, B_75))) | ~v1_funct_1(E_76))), inference(resolution, [status(thm)], [c_42, c_285])).
% 2.73/1.42  tff(c_296, plain, (![A_80, B_81, E_82]: (k1_partfun1(A_80, B_81, '#skF_2', '#skF_3', E_82, '#skF_5')=k5_relat_1(E_82, '#skF_5') | ~m1_subset_1(E_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))) | ~v1_funct_1(E_82))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_287])).
% 2.73/1.42  tff(c_302, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_296])).
% 2.73/1.42  tff(c_308, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_302])).
% 2.73/1.42  tff(c_34, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.73/1.42  tff(c_427, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_308, c_34])).
% 2.73/1.42  tff(c_70, plain, (![C_34, A_35, B_36]: (v1_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.73/1.42  tff(c_77, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_70])).
% 2.73/1.42  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.42  tff(c_38, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.73/1.42  tff(c_79, plain, (![A_37, B_38, C_39]: (k2_relset_1(A_37, B_38, C_39)=k2_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.73/1.42  tff(c_82, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_79])).
% 2.73/1.42  tff(c_87, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_82])).
% 2.73/1.42  tff(c_36, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.73/1.42  tff(c_44, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.73/1.42  tff(c_99, plain, (![A_41, B_42, C_43]: (k1_relset_1(A_41, B_42, C_43)=k1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.73/1.42  tff(c_106, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_99])).
% 2.73/1.42  tff(c_132, plain, (![B_54, A_55, C_56]: (k1_xboole_0=B_54 | k1_relset_1(A_55, B_54, C_56)=A_55 | ~v1_funct_2(C_56, A_55, B_54) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_55, B_54))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.73/1.42  tff(c_135, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_132])).
% 2.73/1.42  tff(c_141, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_106, c_135])).
% 2.73/1.42  tff(c_142, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_36, c_141])).
% 2.73/1.42  tff(c_78, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_70])).
% 2.73/1.42  tff(c_40, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.73/1.42  tff(c_85, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_79])).
% 2.73/1.42  tff(c_89, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_85])).
% 2.73/1.42  tff(c_119, plain, (![B_50, A_51]: (k2_relat_1(k5_relat_1(B_50, A_51))=k2_relat_1(A_51) | ~r1_tarski(k1_relat_1(A_51), k2_relat_1(B_50)) | ~v1_relat_1(B_50) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.73/1.42  tff(c_122, plain, (![A_51]: (k2_relat_1(k5_relat_1('#skF_4', A_51))=k2_relat_1(A_51) | ~r1_tarski(k1_relat_1(A_51), '#skF_2') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_51))), inference(superposition, [status(thm), theory('equality')], [c_89, c_119])).
% 2.73/1.42  tff(c_127, plain, (![A_51]: (k2_relat_1(k5_relat_1('#skF_4', A_51))=k2_relat_1(A_51) | ~r1_tarski(k1_relat_1(A_51), '#skF_2') | ~v1_relat_1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_122])).
% 2.73/1.42  tff(c_153, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_142, c_127])).
% 2.73/1.42  tff(c_162, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_6, c_87, c_153])).
% 2.73/1.42  tff(c_28, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (m1_subset_1(k1_partfun1(A_18, B_19, C_20, D_21, E_22, F_23), k1_zfmisc_1(k2_zfmisc_1(A_18, D_21))) | ~m1_subset_1(F_23, k1_zfmisc_1(k2_zfmisc_1(C_20, D_21))) | ~v1_funct_1(F_23) | ~m1_subset_1(E_22, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))) | ~v1_funct_1(E_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.73/1.42  tff(c_431, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_308, c_28])).
% 2.73/1.42  tff(c_435, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_46, c_42, c_431])).
% 2.73/1.42  tff(c_14, plain, (![A_12, B_13, C_14]: (k2_relset_1(A_12, B_13, C_14)=k2_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.73/1.42  tff(c_487, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_435, c_14])).
% 2.73/1.42  tff(c_517, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_487])).
% 2.73/1.42  tff(c_519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_427, c_517])).
% 2.73/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.42  
% 2.73/1.42  Inference rules
% 2.73/1.42  ----------------------
% 2.73/1.42  #Ref     : 0
% 2.73/1.42  #Sup     : 102
% 2.73/1.42  #Fact    : 0
% 2.73/1.42  #Define  : 0
% 2.73/1.42  #Split   : 6
% 2.73/1.42  #Chain   : 0
% 2.73/1.42  #Close   : 0
% 2.73/1.42  
% 2.73/1.42  Ordering : KBO
% 2.73/1.42  
% 2.73/1.42  Simplification rules
% 2.73/1.42  ----------------------
% 2.73/1.42  #Subsume      : 5
% 2.73/1.42  #Demod        : 71
% 2.73/1.42  #Tautology    : 31
% 2.73/1.42  #SimpNegUnit  : 7
% 2.73/1.42  #BackRed      : 5
% 2.73/1.42  
% 2.73/1.42  #Partial instantiations: 0
% 2.73/1.42  #Strategies tried      : 1
% 2.73/1.42  
% 2.73/1.42  Timing (in seconds)
% 2.73/1.42  ----------------------
% 2.73/1.42  Preprocessing        : 0.34
% 2.73/1.42  Parsing              : 0.19
% 2.73/1.42  CNF conversion       : 0.02
% 2.73/1.42  Main loop            : 0.28
% 2.73/1.42  Inferencing          : 0.10
% 2.73/1.42  Reduction            : 0.09
% 2.73/1.42  Demodulation         : 0.06
% 2.73/1.42  BG Simplification    : 0.02
% 2.73/1.42  Subsumption          : 0.05
% 2.73/1.42  Abstraction          : 0.01
% 2.73/1.42  MUC search           : 0.00
% 2.73/1.42  Cooper               : 0.00
% 2.73/1.42  Total                : 0.65
% 2.73/1.42  Index Insertion      : 0.00
% 2.73/1.42  Index Deletion       : 0.00
% 2.73/1.42  Index Matching       : 0.00
% 2.73/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
