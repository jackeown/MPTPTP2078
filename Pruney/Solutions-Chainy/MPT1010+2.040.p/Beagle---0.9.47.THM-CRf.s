%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:10 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 108 expanded)
%              Number of leaves         :   38 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  105 ( 203 expanded)
%              Number of equality atoms :   33 (  68 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
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

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    k1_funct_1('#skF_7','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4',k1_tarski('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_195,plain,(
    ! [C_61,B_62,A_63] :
      ( v5_relat_1(C_61,B_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_199,plain,(
    v5_relat_1('#skF_7',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_58,c_195])).

tff(c_56,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_117,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_121,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_117])).

tff(c_62,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_60,plain,(
    v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_265,plain,(
    ! [A_69,B_70,C_71] :
      ( k1_relset_1(A_69,B_70,C_71) = k1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_269,plain,(
    k1_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_265])).

tff(c_311,plain,(
    ! [B_94,A_95,C_96] :
      ( k1_xboole_0 = B_94
      | k1_relset_1(A_95,B_94,C_96) = A_95
      | ~ v1_funct_2(C_96,A_95,B_94)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_314,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | k1_relset_1('#skF_4',k1_tarski('#skF_5'),'#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_58,c_311])).

tff(c_317,plain,
    ( k1_tarski('#skF_5') = k1_xboole_0
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_269,c_314])).

tff(c_318,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_317])).

tff(c_32,plain,(
    ! [C_18,B_17,A_16] :
      ( m1_subset_1(k1_funct_1(C_18,B_17),A_16)
      | ~ r2_hidden(B_17,k1_relat_1(C_18))
      | ~ v1_funct_1(C_18)
      | ~ v5_relat_1(C_18,A_16)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_322,plain,(
    ! [B_17,A_16] :
      ( m1_subset_1(k1_funct_1('#skF_7',B_17),A_16)
      | ~ r2_hidden(B_17,'#skF_4')
      | ~ v1_funct_1('#skF_7')
      | ~ v5_relat_1('#skF_7',A_16)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_32])).

tff(c_332,plain,(
    ! [B_97,A_98] :
      ( m1_subset_1(k1_funct_1('#skF_7',B_97),A_98)
      | ~ r2_hidden(B_97,'#skF_4')
      | ~ v5_relat_1('#skF_7',A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_62,c_322])).

tff(c_26,plain,(
    ! [A_11] : k2_tarski(A_11,A_11) = k1_tarski(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_77,plain,(
    ! [D_34,B_35] : r2_hidden(D_34,k2_tarski(D_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    ! [D_36,B_37] : ~ v1_xboole_0(k2_tarski(D_36,B_37)) ),
    inference(resolution,[status(thm)],[c_77,c_2])).

tff(c_87,plain,(
    ! [A_11] : ~ v1_xboole_0(k1_tarski(A_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_85])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | v1_xboole_0(B_15)
      | ~ m1_subset_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_127,plain,(
    ! [D_50,B_51,A_52] :
      ( D_50 = B_51
      | D_50 = A_52
      | ~ r2_hidden(D_50,k2_tarski(A_52,B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_155,plain,(
    ! [D_53,A_54] :
      ( D_53 = A_54
      | D_53 = A_54
      | ~ r2_hidden(D_53,k1_tarski(A_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_127])).

tff(c_159,plain,(
    ! [A_54,A_14] :
      ( A_54 = A_14
      | v1_xboole_0(k1_tarski(A_54))
      | ~ m1_subset_1(A_14,k1_tarski(A_54)) ) ),
    inference(resolution,[status(thm)],[c_30,c_155])).

tff(c_169,plain,(
    ! [A_54,A_14] :
      ( A_54 = A_14
      | ~ m1_subset_1(A_14,k1_tarski(A_54)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_159])).

tff(c_925,plain,(
    ! [B_1137,A_1138] :
      ( k1_funct_1('#skF_7',B_1137) = A_1138
      | ~ r2_hidden(B_1137,'#skF_4')
      | ~ v5_relat_1('#skF_7',k1_tarski(A_1138)) ) ),
    inference(resolution,[status(thm)],[c_332,c_169])).

tff(c_941,plain,(
    ! [A_1161] :
      ( k1_funct_1('#skF_7','#skF_6') = A_1161
      | ~ v5_relat_1('#skF_7',k1_tarski(A_1161)) ) ),
    inference(resolution,[status(thm)],[c_56,c_925])).

tff(c_945,plain,(
    k1_funct_1('#skF_7','#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_199,c_941])).

tff(c_949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_945])).

tff(c_950,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_970,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_950,c_87])).

tff(c_975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_970])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:52:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.42  
% 2.78/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.43  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.78/1.43  
% 2.78/1.43  %Foreground sorts:
% 2.78/1.43  
% 2.78/1.43  
% 2.78/1.43  %Background operators:
% 2.78/1.43  
% 2.78/1.43  
% 2.78/1.43  %Foreground operators:
% 2.78/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.78/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.78/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.78/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.78/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.78/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.78/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.78/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.78/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.78/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.78/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.78/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.78/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.78/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.78/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.43  
% 2.78/1.44  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.78/1.44  tff(f_104, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.78/1.44  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.78/1.44  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.78/1.44  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.78/1.44  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.78/1.44  tff(f_61, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 2.78/1.44  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.78/1.44  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.78/1.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.78/1.44  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.78/1.44  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.78/1.44  tff(c_54, plain, (k1_funct_1('#skF_7', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.78/1.44  tff(c_58, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', k1_tarski('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.78/1.44  tff(c_195, plain, (![C_61, B_62, A_63]: (v5_relat_1(C_61, B_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.78/1.44  tff(c_199, plain, (v5_relat_1('#skF_7', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_195])).
% 2.78/1.44  tff(c_56, plain, (r2_hidden('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.78/1.44  tff(c_117, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.78/1.44  tff(c_121, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_117])).
% 2.78/1.44  tff(c_62, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.78/1.44  tff(c_60, plain, (v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.78/1.44  tff(c_265, plain, (![A_69, B_70, C_71]: (k1_relset_1(A_69, B_70, C_71)=k1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.78/1.44  tff(c_269, plain, (k1_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_265])).
% 2.78/1.44  tff(c_311, plain, (![B_94, A_95, C_96]: (k1_xboole_0=B_94 | k1_relset_1(A_95, B_94, C_96)=A_95 | ~v1_funct_2(C_96, A_95, B_94) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.78/1.44  tff(c_314, plain, (k1_tarski('#skF_5')=k1_xboole_0 | k1_relset_1('#skF_4', k1_tarski('#skF_5'), '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_58, c_311])).
% 2.78/1.44  tff(c_317, plain, (k1_tarski('#skF_5')=k1_xboole_0 | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_269, c_314])).
% 2.78/1.44  tff(c_318, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_317])).
% 2.78/1.44  tff(c_32, plain, (![C_18, B_17, A_16]: (m1_subset_1(k1_funct_1(C_18, B_17), A_16) | ~r2_hidden(B_17, k1_relat_1(C_18)) | ~v1_funct_1(C_18) | ~v5_relat_1(C_18, A_16) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.78/1.44  tff(c_322, plain, (![B_17, A_16]: (m1_subset_1(k1_funct_1('#skF_7', B_17), A_16) | ~r2_hidden(B_17, '#skF_4') | ~v1_funct_1('#skF_7') | ~v5_relat_1('#skF_7', A_16) | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_318, c_32])).
% 2.78/1.44  tff(c_332, plain, (![B_97, A_98]: (m1_subset_1(k1_funct_1('#skF_7', B_97), A_98) | ~r2_hidden(B_97, '#skF_4') | ~v5_relat_1('#skF_7', A_98))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_62, c_322])).
% 2.78/1.44  tff(c_26, plain, (![A_11]: (k2_tarski(A_11, A_11)=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.78/1.44  tff(c_77, plain, (![D_34, B_35]: (r2_hidden(D_34, k2_tarski(D_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.78/1.44  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.78/1.44  tff(c_85, plain, (![D_36, B_37]: (~v1_xboole_0(k2_tarski(D_36, B_37)))), inference(resolution, [status(thm)], [c_77, c_2])).
% 2.78/1.44  tff(c_87, plain, (![A_11]: (~v1_xboole_0(k1_tarski(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_85])).
% 2.78/1.44  tff(c_30, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | v1_xboole_0(B_15) | ~m1_subset_1(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.78/1.44  tff(c_127, plain, (![D_50, B_51, A_52]: (D_50=B_51 | D_50=A_52 | ~r2_hidden(D_50, k2_tarski(A_52, B_51)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.78/1.44  tff(c_155, plain, (![D_53, A_54]: (D_53=A_54 | D_53=A_54 | ~r2_hidden(D_53, k1_tarski(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_127])).
% 2.78/1.44  tff(c_159, plain, (![A_54, A_14]: (A_54=A_14 | v1_xboole_0(k1_tarski(A_54)) | ~m1_subset_1(A_14, k1_tarski(A_54)))), inference(resolution, [status(thm)], [c_30, c_155])).
% 2.78/1.44  tff(c_169, plain, (![A_54, A_14]: (A_54=A_14 | ~m1_subset_1(A_14, k1_tarski(A_54)))), inference(negUnitSimplification, [status(thm)], [c_87, c_159])).
% 2.78/1.44  tff(c_925, plain, (![B_1137, A_1138]: (k1_funct_1('#skF_7', B_1137)=A_1138 | ~r2_hidden(B_1137, '#skF_4') | ~v5_relat_1('#skF_7', k1_tarski(A_1138)))), inference(resolution, [status(thm)], [c_332, c_169])).
% 2.78/1.44  tff(c_941, plain, (![A_1161]: (k1_funct_1('#skF_7', '#skF_6')=A_1161 | ~v5_relat_1('#skF_7', k1_tarski(A_1161)))), inference(resolution, [status(thm)], [c_56, c_925])).
% 2.78/1.44  tff(c_945, plain, (k1_funct_1('#skF_7', '#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_199, c_941])).
% 2.78/1.44  tff(c_949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_945])).
% 2.78/1.44  tff(c_950, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_317])).
% 2.78/1.44  tff(c_970, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_950, c_87])).
% 2.78/1.44  tff(c_975, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_970])).
% 2.78/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.44  
% 2.78/1.44  Inference rules
% 2.78/1.44  ----------------------
% 2.78/1.44  #Ref     : 0
% 2.78/1.44  #Sup     : 130
% 2.78/1.44  #Fact    : 4
% 2.78/1.44  #Define  : 0
% 2.78/1.44  #Split   : 1
% 2.78/1.44  #Chain   : 0
% 2.78/1.44  #Close   : 0
% 2.78/1.44  
% 2.78/1.44  Ordering : KBO
% 2.78/1.44  
% 2.78/1.44  Simplification rules
% 2.78/1.44  ----------------------
% 2.78/1.44  #Subsume      : 11
% 2.78/1.44  #Demod        : 28
% 2.78/1.44  #Tautology    : 35
% 2.78/1.44  #SimpNegUnit  : 10
% 2.78/1.44  #BackRed      : 5
% 2.78/1.44  
% 2.78/1.44  #Partial instantiations: 752
% 2.78/1.44  #Strategies tried      : 1
% 2.78/1.44  
% 2.78/1.44  Timing (in seconds)
% 2.78/1.44  ----------------------
% 2.78/1.44  Preprocessing        : 0.32
% 2.78/1.44  Parsing              : 0.16
% 2.78/1.44  CNF conversion       : 0.02
% 2.78/1.44  Main loop            : 0.35
% 2.78/1.44  Inferencing          : 0.17
% 2.78/1.44  Reduction            : 0.08
% 2.78/1.44  Demodulation         : 0.06
% 2.78/1.44  BG Simplification    : 0.02
% 2.78/1.44  Subsumption          : 0.05
% 2.78/1.44  Abstraction          : 0.02
% 2.78/1.44  MUC search           : 0.00
% 2.78/1.44  Cooper               : 0.00
% 2.78/1.44  Total                : 0.70
% 2.78/1.44  Index Insertion      : 0.00
% 2.78/1.44  Index Deletion       : 0.00
% 2.78/1.44  Index Matching       : 0.00
% 2.78/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
