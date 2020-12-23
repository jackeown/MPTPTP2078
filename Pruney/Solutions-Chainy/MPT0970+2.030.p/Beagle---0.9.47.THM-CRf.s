%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:23 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 101 expanded)
%              Number of leaves         :   31 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 ( 253 expanded)
%              Number of equality atoms :   34 (  83 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(E,D),C) )
      <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_88,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_36,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_157,plain,(
    ! [A_72,B_73,C_74] :
      ( r2_hidden('#skF_1'(A_72,B_73,C_74),B_73)
      | k2_relset_1(A_72,B_73,C_74) = B_73
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_159,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_157])).

tff(c_162,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_159])).

tff(c_46,plain,(
    ! [D_34] :
      ( r2_hidden('#skF_6'(D_34),'#skF_3')
      | ~ r2_hidden(D_34,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_40,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_75,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_relset_1(A_48,B_49,C_50) = k1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_79,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_75])).

tff(c_116,plain,(
    ! [B_65,A_66,C_67] :
      ( k1_xboole_0 = B_65
      | k1_relset_1(A_66,B_65,C_67) = A_66
      | ~ v1_funct_2(C_67,A_66,B_65)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_119,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_116])).

tff(c_122,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_79,c_119])).

tff(c_123,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_64,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_68,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_64])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_44,plain,(
    ! [D_34] :
      ( k1_funct_1('#skF_5','#skF_6'(D_34)) = D_34
      | ~ r2_hidden(D_34,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_86,plain,(
    ! [B_55,A_56] :
      ( r2_hidden(k4_tarski(B_55,k1_funct_1(A_56,B_55)),A_56)
      | ~ r2_hidden(B_55,k1_relat_1(A_56))
      | ~ v1_funct_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_92,plain,(
    ! [D_34] :
      ( r2_hidden(k4_tarski('#skF_6'(D_34),D_34),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_34),k1_relat_1('#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ r2_hidden(D_34,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_86])).

tff(c_95,plain,(
    ! [D_34] :
      ( r2_hidden(k4_tarski('#skF_6'(D_34),D_34),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_34),k1_relat_1('#skF_5'))
      | ~ r2_hidden(D_34,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_42,c_92])).

tff(c_125,plain,(
    ! [D_34] :
      ( r2_hidden(k4_tarski('#skF_6'(D_34),D_34),'#skF_5')
      | ~ r2_hidden('#skF_6'(D_34),'#skF_3')
      | ~ r2_hidden(D_34,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_95])).

tff(c_197,plain,(
    ! [E_81,A_82,B_83,C_84] :
      ( ~ r2_hidden(k4_tarski(E_81,'#skF_1'(A_82,B_83,C_84)),C_84)
      | k2_relset_1(A_82,B_83,C_84) = B_83
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_304,plain,(
    ! [A_116,B_117] :
      ( k2_relset_1(A_116,B_117,'#skF_5') = B_117
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ r2_hidden('#skF_6'('#skF_1'(A_116,B_117,'#skF_5')),'#skF_3')
      | ~ r2_hidden('#skF_1'(A_116,B_117,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_125,c_197])).

tff(c_313,plain,(
    ! [A_118,B_119] :
      ( k2_relset_1(A_118,B_119,'#skF_5') = B_119
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ r2_hidden('#skF_1'(A_118,B_119,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_304])).

tff(c_316,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4'
    | ~ r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_313])).

tff(c_319,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_316])).

tff(c_321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_319])).

tff(c_322,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_332,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_2])).

tff(c_367,plain,(
    ! [A_129,B_130,C_131] :
      ( r2_hidden('#skF_1'(A_129,B_130,C_131),B_130)
      | k2_relset_1(A_129,B_130,C_131) = B_130
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_369,plain,
    ( r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_367])).

tff(c_372,plain,(
    r2_hidden('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_369])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( ~ r1_tarski(B_8,A_7)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_375,plain,(
    ~ r1_tarski('#skF_4','#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_372,c_12])).

tff(c_379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_375])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:02:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.53  
% 2.90/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.54  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_6
% 2.90/1.54  
% 2.90/1.54  %Foreground sorts:
% 2.90/1.54  
% 2.90/1.54  
% 2.90/1.54  %Background operators:
% 2.90/1.54  
% 2.90/1.54  
% 2.90/1.54  %Foreground operators:
% 2.90/1.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.90/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.90/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.90/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.54  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.90/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.90/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.54  tff('#skF_5', type, '#skF_5': $i).
% 2.90/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.90/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.90/1.54  tff('#skF_3', type, '#skF_3': $i).
% 2.90/1.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.90/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.90/1.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.90/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.90/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.90/1.54  tff('#skF_4', type, '#skF_4': $i).
% 2.90/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.90/1.54  tff('#skF_6', type, '#skF_6': $i > $i).
% 2.90/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.90/1.54  
% 2.90/1.55  tff(f_107, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 2.90/1.55  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(E, D), C)))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relset_1)).
% 2.90/1.55  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.90/1.55  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.90/1.55  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.90/1.55  tff(f_45, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 2.90/1.55  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.90/1.55  tff(f_50, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.90/1.55  tff(c_36, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.90/1.55  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.90/1.55  tff(c_157, plain, (![A_72, B_73, C_74]: (r2_hidden('#skF_1'(A_72, B_73, C_74), B_73) | k2_relset_1(A_72, B_73, C_74)=B_73 | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.90/1.55  tff(c_159, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_38, c_157])).
% 2.90/1.55  tff(c_162, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_36, c_159])).
% 2.90/1.55  tff(c_46, plain, (![D_34]: (r2_hidden('#skF_6'(D_34), '#skF_3') | ~r2_hidden(D_34, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.90/1.55  tff(c_40, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.90/1.55  tff(c_75, plain, (![A_48, B_49, C_50]: (k1_relset_1(A_48, B_49, C_50)=k1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.90/1.55  tff(c_79, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_75])).
% 2.90/1.55  tff(c_116, plain, (![B_65, A_66, C_67]: (k1_xboole_0=B_65 | k1_relset_1(A_66, B_65, C_67)=A_66 | ~v1_funct_2(C_67, A_66, B_65) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.90/1.55  tff(c_119, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_116])).
% 2.90/1.55  tff(c_122, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_79, c_119])).
% 2.90/1.55  tff(c_123, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_122])).
% 2.90/1.55  tff(c_64, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.90/1.55  tff(c_68, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_64])).
% 2.90/1.55  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.90/1.55  tff(c_44, plain, (![D_34]: (k1_funct_1('#skF_5', '#skF_6'(D_34))=D_34 | ~r2_hidden(D_34, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.90/1.55  tff(c_86, plain, (![B_55, A_56]: (r2_hidden(k4_tarski(B_55, k1_funct_1(A_56, B_55)), A_56) | ~r2_hidden(B_55, k1_relat_1(A_56)) | ~v1_funct_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.90/1.55  tff(c_92, plain, (![D_34]: (r2_hidden(k4_tarski('#skF_6'(D_34), D_34), '#skF_5') | ~r2_hidden('#skF_6'(D_34), k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r2_hidden(D_34, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_86])).
% 2.90/1.55  tff(c_95, plain, (![D_34]: (r2_hidden(k4_tarski('#skF_6'(D_34), D_34), '#skF_5') | ~r2_hidden('#skF_6'(D_34), k1_relat_1('#skF_5')) | ~r2_hidden(D_34, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_42, c_92])).
% 2.90/1.55  tff(c_125, plain, (![D_34]: (r2_hidden(k4_tarski('#skF_6'(D_34), D_34), '#skF_5') | ~r2_hidden('#skF_6'(D_34), '#skF_3') | ~r2_hidden(D_34, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_95])).
% 2.90/1.55  tff(c_197, plain, (![E_81, A_82, B_83, C_84]: (~r2_hidden(k4_tarski(E_81, '#skF_1'(A_82, B_83, C_84)), C_84) | k2_relset_1(A_82, B_83, C_84)=B_83 | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.90/1.55  tff(c_304, plain, (![A_116, B_117]: (k2_relset_1(A_116, B_117, '#skF_5')=B_117 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~r2_hidden('#skF_6'('#skF_1'(A_116, B_117, '#skF_5')), '#skF_3') | ~r2_hidden('#skF_1'(A_116, B_117, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_125, c_197])).
% 2.90/1.55  tff(c_313, plain, (![A_118, B_119]: (k2_relset_1(A_118, B_119, '#skF_5')=B_119 | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | ~r2_hidden('#skF_1'(A_118, B_119, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_304])).
% 2.90/1.55  tff(c_316, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4' | ~r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_38, c_313])).
% 2.90/1.55  tff(c_319, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_316])).
% 2.90/1.55  tff(c_321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_319])).
% 2.90/1.55  tff(c_322, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_122])).
% 2.90/1.55  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.90/1.55  tff(c_332, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_2])).
% 2.90/1.55  tff(c_367, plain, (![A_129, B_130, C_131]: (r2_hidden('#skF_1'(A_129, B_130, C_131), B_130) | k2_relset_1(A_129, B_130, C_131)=B_130 | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.90/1.55  tff(c_369, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_38, c_367])).
% 2.90/1.55  tff(c_372, plain, (r2_hidden('#skF_1'('#skF_3', '#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_36, c_369])).
% 2.90/1.55  tff(c_12, plain, (![B_8, A_7]: (~r1_tarski(B_8, A_7) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.90/1.55  tff(c_375, plain, (~r1_tarski('#skF_4', '#skF_1'('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_372, c_12])).
% 2.90/1.55  tff(c_379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_332, c_375])).
% 2.90/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.90/1.55  
% 2.90/1.55  Inference rules
% 2.90/1.55  ----------------------
% 2.90/1.55  #Ref     : 0
% 2.90/1.55  #Sup     : 63
% 2.90/1.55  #Fact    : 0
% 2.90/1.55  #Define  : 0
% 2.90/1.55  #Split   : 5
% 2.90/1.55  #Chain   : 0
% 2.90/1.55  #Close   : 0
% 2.90/1.55  
% 2.90/1.55  Ordering : KBO
% 2.90/1.55  
% 2.90/1.55  Simplification rules
% 2.90/1.55  ----------------------
% 2.90/1.55  #Subsume      : 23
% 2.90/1.55  #Demod        : 57
% 2.90/1.55  #Tautology    : 13
% 2.90/1.55  #SimpNegUnit  : 5
% 2.90/1.55  #BackRed      : 14
% 2.90/1.55  
% 2.90/1.55  #Partial instantiations: 0
% 2.90/1.55  #Strategies tried      : 1
% 2.90/1.55  
% 2.90/1.55  Timing (in seconds)
% 2.90/1.55  ----------------------
% 2.90/1.56  Preprocessing        : 0.38
% 2.90/1.56  Parsing              : 0.21
% 2.90/1.56  CNF conversion       : 0.03
% 2.90/1.56  Main loop            : 0.33
% 3.03/1.56  Inferencing          : 0.13
% 3.03/1.56  Reduction            : 0.09
% 3.03/1.56  Demodulation         : 0.06
% 3.03/1.56  BG Simplification    : 0.02
% 3.03/1.56  Subsumption          : 0.06
% 3.03/1.56  Abstraction          : 0.02
% 3.03/1.56  MUC search           : 0.00
% 3.03/1.56  Cooper               : 0.00
% 3.03/1.56  Total                : 0.75
% 3.03/1.56  Index Insertion      : 0.00
% 3.03/1.56  Index Deletion       : 0.00
% 3.03/1.56  Index Matching       : 0.00
% 3.03/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
