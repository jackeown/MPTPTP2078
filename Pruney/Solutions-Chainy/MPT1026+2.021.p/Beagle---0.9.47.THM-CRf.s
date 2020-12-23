%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:42 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 128 expanded)
%              Number of leaves         :   24 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :   94 ( 305 expanded)
%              Number of equality atoms :   15 (  62 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_46,plain,(
    r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_73,plain,(
    ! [A_40,B_41,D_42] :
      ( '#skF_4'(A_40,B_41,k1_funct_2(A_40,B_41),D_42) = D_42
      | ~ r2_hidden(D_42,k1_funct_2(A_40,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_76,plain,(
    '#skF_4'('#skF_5','#skF_6',k1_funct_2('#skF_5','#skF_6'),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_46,c_73])).

tff(c_135,plain,(
    ! [A_51,B_52,D_53] :
      ( r1_tarski(k2_relat_1('#skF_4'(A_51,B_52,k1_funct_2(A_51,B_52),D_53)),B_52)
      | ~ r2_hidden(D_53,k1_funct_2(A_51,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_138,plain,
    ( r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_135])).

tff(c_140,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_138])).

tff(c_12,plain,(
    ! [A_1,B_2,D_17] :
      ( v1_relat_1('#skF_4'(A_1,B_2,k1_funct_2(A_1,B_2),D_17))
      | ~ r2_hidden(D_17,k1_funct_2(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,
    ( v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_12])).

tff(c_87,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_80])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_47,plain,(
    ~ v1_funct_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_49,plain,(
    ! [A_26,B_27,D_28] :
      ( '#skF_4'(A_26,B_27,k1_funct_2(A_26,B_27),D_28) = D_28
      | ~ r2_hidden(D_28,k1_funct_2(A_26,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_52,plain,(
    '#skF_4'('#skF_5','#skF_6',k1_funct_2('#skF_5','#skF_6'),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_46,c_49])).

tff(c_10,plain,(
    ! [A_1,B_2,D_17] :
      ( v1_funct_1('#skF_4'(A_1,B_2,k1_funct_2(A_1,B_2),D_17))
      | ~ r2_hidden(D_17,k1_funct_2(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_57,plain,
    ( v1_funct_1('#skF_7')
    | ~ r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_10])).

tff(c_64,plain,(
    v1_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_57])).

tff(c_66,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_64])).

tff(c_68,plain,(
    v1_funct_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_91,plain,(
    ! [A_43,B_44,D_45] :
      ( k1_relat_1('#skF_4'(A_43,B_44,k1_funct_2(A_43,B_44),D_45)) = A_43
      | ~ r2_hidden(D_45,k1_funct_2(A_43,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_103,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_91])).

tff(c_107,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_103])).

tff(c_159,plain,(
    ! [B_60,A_61] :
      ( m1_subset_1(B_60,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_60),A_61)))
      | ~ r1_tarski(k2_relat_1(B_60),A_61)
      | ~ v1_funct_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_162,plain,(
    ! [A_61] :
      ( m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_61)))
      | ~ r1_tarski(k2_relat_1('#skF_7'),A_61)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_159])).

tff(c_168,plain,(
    ! [A_62] :
      ( m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',A_62)))
      | ~ r1_tarski(k2_relat_1('#skF_7'),A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_68,c_162])).

tff(c_67,plain,
    ( ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_69,plain,(
    ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_171,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_168,c_69])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_171])).

tff(c_176,plain,(
    ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_181,plain,(
    ! [A_71,B_72,D_73] :
      ( '#skF_4'(A_71,B_72,k1_funct_2(A_71,B_72),D_73) = D_73
      | ~ r2_hidden(D_73,k1_funct_2(A_71,B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_184,plain,(
    '#skF_4'('#skF_5','#skF_6',k1_funct_2('#skF_5','#skF_6'),'#skF_7') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_46,c_181])).

tff(c_243,plain,(
    ! [A_82,B_83,D_84] :
      ( r1_tarski(k2_relat_1('#skF_4'(A_82,B_83,k1_funct_2(A_82,B_83),D_84)),B_83)
      | ~ r2_hidden(D_84,k1_funct_2(A_82,B_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_246,plain,
    ( r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_243])).

tff(c_248,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_246])).

tff(c_203,plain,
    ( v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_12])).

tff(c_212,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_203])).

tff(c_6,plain,(
    ! [A_1,B_2,D_17] :
      ( k1_relat_1('#skF_4'(A_1,B_2,k1_funct_2(A_1,B_2),D_17)) = A_1
      | ~ r2_hidden(D_17,k1_funct_2(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_200,plain,
    ( k1_relat_1('#skF_7') = '#skF_5'
    | ~ r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_6])).

tff(c_210,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_200])).

tff(c_40,plain,(
    ! [B_22,A_21] :
      ( v1_funct_2(B_22,k1_relat_1(B_22),A_21)
      | ~ r1_tarski(k2_relat_1(B_22),A_21)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_219,plain,(
    ! [A_21] :
      ( v1_funct_2('#skF_7','#skF_5',A_21)
      | ~ r1_tarski(k2_relat_1('#skF_7'),A_21)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_40])).

tff(c_223,plain,(
    ! [A_21] :
      ( v1_funct_2('#skF_7','#skF_5',A_21)
      | ~ r1_tarski(k2_relat_1('#skF_7'),A_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_68,c_219])).

tff(c_253,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_248,c_223])).

tff(c_259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_253])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:29:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.23  
% 2.15/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.24  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.15/1.24  
% 2.15/1.24  %Foreground sorts:
% 2.15/1.24  
% 2.15/1.24  
% 2.15/1.24  %Background operators:
% 2.15/1.24  
% 2.15/1.24  
% 2.15/1.24  %Foreground operators:
% 2.15/1.24  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.15/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.15/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.24  tff('#skF_7', type, '#skF_7': $i).
% 2.15/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.15/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.15/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.15/1.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.15/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.24  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.15/1.24  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 2.15/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.15/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.15/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.24  
% 2.15/1.25  tff(f_62, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 2.15/1.25  tff(f_41, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 2.15/1.25  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 2.15/1.25  tff(c_46, plain, (r2_hidden('#skF_7', k1_funct_2('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.15/1.25  tff(c_73, plain, (![A_40, B_41, D_42]: ('#skF_4'(A_40, B_41, k1_funct_2(A_40, B_41), D_42)=D_42 | ~r2_hidden(D_42, k1_funct_2(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.25  tff(c_76, plain, ('#skF_4'('#skF_5', '#skF_6', k1_funct_2('#skF_5', '#skF_6'), '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_46, c_73])).
% 2.15/1.25  tff(c_135, plain, (![A_51, B_52, D_53]: (r1_tarski(k2_relat_1('#skF_4'(A_51, B_52, k1_funct_2(A_51, B_52), D_53)), B_52) | ~r2_hidden(D_53, k1_funct_2(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.25  tff(c_138, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_6') | ~r2_hidden('#skF_7', k1_funct_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_135])).
% 2.15/1.25  tff(c_140, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_138])).
% 2.15/1.25  tff(c_12, plain, (![A_1, B_2, D_17]: (v1_relat_1('#skF_4'(A_1, B_2, k1_funct_2(A_1, B_2), D_17)) | ~r2_hidden(D_17, k1_funct_2(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.25  tff(c_80, plain, (v1_relat_1('#skF_7') | ~r2_hidden('#skF_7', k1_funct_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_12])).
% 2.15/1.25  tff(c_87, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_80])).
% 2.15/1.25  tff(c_44, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.15/1.25  tff(c_47, plain, (~v1_funct_1('#skF_7')), inference(splitLeft, [status(thm)], [c_44])).
% 2.15/1.25  tff(c_49, plain, (![A_26, B_27, D_28]: ('#skF_4'(A_26, B_27, k1_funct_2(A_26, B_27), D_28)=D_28 | ~r2_hidden(D_28, k1_funct_2(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.25  tff(c_52, plain, ('#skF_4'('#skF_5', '#skF_6', k1_funct_2('#skF_5', '#skF_6'), '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_46, c_49])).
% 2.15/1.25  tff(c_10, plain, (![A_1, B_2, D_17]: (v1_funct_1('#skF_4'(A_1, B_2, k1_funct_2(A_1, B_2), D_17)) | ~r2_hidden(D_17, k1_funct_2(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.25  tff(c_57, plain, (v1_funct_1('#skF_7') | ~r2_hidden('#skF_7', k1_funct_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_10])).
% 2.15/1.25  tff(c_64, plain, (v1_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_57])).
% 2.15/1.25  tff(c_66, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_64])).
% 2.15/1.25  tff(c_68, plain, (v1_funct_1('#skF_7')), inference(splitRight, [status(thm)], [c_44])).
% 2.15/1.25  tff(c_91, plain, (![A_43, B_44, D_45]: (k1_relat_1('#skF_4'(A_43, B_44, k1_funct_2(A_43, B_44), D_45))=A_43 | ~r2_hidden(D_45, k1_funct_2(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.25  tff(c_103, plain, (k1_relat_1('#skF_7')='#skF_5' | ~r2_hidden('#skF_7', k1_funct_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_76, c_91])).
% 2.15/1.25  tff(c_107, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_103])).
% 2.15/1.25  tff(c_159, plain, (![B_60, A_61]: (m1_subset_1(B_60, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_60), A_61))) | ~r1_tarski(k2_relat_1(B_60), A_61) | ~v1_funct_1(B_60) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.15/1.25  tff(c_162, plain, (![A_61]: (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_61))) | ~r1_tarski(k2_relat_1('#skF_7'), A_61) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_107, c_159])).
% 2.15/1.25  tff(c_168, plain, (![A_62]: (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', A_62))) | ~r1_tarski(k2_relat_1('#skF_7'), A_62))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_68, c_162])).
% 2.15/1.25  tff(c_67, plain, (~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_44])).
% 2.15/1.25  tff(c_69, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_67])).
% 2.15/1.25  tff(c_171, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_168, c_69])).
% 2.15/1.25  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_171])).
% 2.15/1.25  tff(c_176, plain, (~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_67])).
% 2.15/1.25  tff(c_181, plain, (![A_71, B_72, D_73]: ('#skF_4'(A_71, B_72, k1_funct_2(A_71, B_72), D_73)=D_73 | ~r2_hidden(D_73, k1_funct_2(A_71, B_72)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.25  tff(c_184, plain, ('#skF_4'('#skF_5', '#skF_6', k1_funct_2('#skF_5', '#skF_6'), '#skF_7')='#skF_7'), inference(resolution, [status(thm)], [c_46, c_181])).
% 2.15/1.25  tff(c_243, plain, (![A_82, B_83, D_84]: (r1_tarski(k2_relat_1('#skF_4'(A_82, B_83, k1_funct_2(A_82, B_83), D_84)), B_83) | ~r2_hidden(D_84, k1_funct_2(A_82, B_83)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.25  tff(c_246, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_6') | ~r2_hidden('#skF_7', k1_funct_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_184, c_243])).
% 2.15/1.25  tff(c_248, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_246])).
% 2.15/1.25  tff(c_203, plain, (v1_relat_1('#skF_7') | ~r2_hidden('#skF_7', k1_funct_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_184, c_12])).
% 2.15/1.25  tff(c_212, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_203])).
% 2.15/1.25  tff(c_6, plain, (![A_1, B_2, D_17]: (k1_relat_1('#skF_4'(A_1, B_2, k1_funct_2(A_1, B_2), D_17))=A_1 | ~r2_hidden(D_17, k1_funct_2(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.25  tff(c_200, plain, (k1_relat_1('#skF_7')='#skF_5' | ~r2_hidden('#skF_7', k1_funct_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_184, c_6])).
% 2.15/1.25  tff(c_210, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_200])).
% 2.15/1.25  tff(c_40, plain, (![B_22, A_21]: (v1_funct_2(B_22, k1_relat_1(B_22), A_21) | ~r1_tarski(k2_relat_1(B_22), A_21) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.15/1.25  tff(c_219, plain, (![A_21]: (v1_funct_2('#skF_7', '#skF_5', A_21) | ~r1_tarski(k2_relat_1('#skF_7'), A_21) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_210, c_40])).
% 2.15/1.25  tff(c_223, plain, (![A_21]: (v1_funct_2('#skF_7', '#skF_5', A_21) | ~r1_tarski(k2_relat_1('#skF_7'), A_21))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_68, c_219])).
% 2.15/1.25  tff(c_253, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_248, c_223])).
% 2.15/1.25  tff(c_259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_253])).
% 2.15/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.25  
% 2.15/1.25  Inference rules
% 2.15/1.25  ----------------------
% 2.15/1.25  #Ref     : 0
% 2.15/1.25  #Sup     : 48
% 2.15/1.25  #Fact    : 0
% 2.15/1.25  #Define  : 0
% 2.15/1.25  #Split   : 2
% 2.15/1.25  #Chain   : 0
% 2.15/1.25  #Close   : 0
% 2.15/1.25  
% 2.15/1.25  Ordering : KBO
% 2.15/1.25  
% 2.15/1.25  Simplification rules
% 2.15/1.25  ----------------------
% 2.15/1.25  #Subsume      : 0
% 2.15/1.25  #Demod        : 24
% 2.15/1.25  #Tautology    : 18
% 2.15/1.25  #SimpNegUnit  : 2
% 2.15/1.25  #BackRed      : 0
% 2.15/1.25  
% 2.15/1.25  #Partial instantiations: 0
% 2.15/1.25  #Strategies tried      : 1
% 2.15/1.25  
% 2.15/1.25  Timing (in seconds)
% 2.15/1.25  ----------------------
% 2.15/1.25  Preprocessing        : 0.32
% 2.15/1.25  Parsing              : 0.15
% 2.15/1.26  CNF conversion       : 0.02
% 2.15/1.26  Main loop            : 0.18
% 2.15/1.26  Inferencing          : 0.07
% 2.15/1.26  Reduction            : 0.05
% 2.15/1.26  Demodulation         : 0.04
% 2.15/1.26  BG Simplification    : 0.02
% 2.15/1.26  Subsumption          : 0.02
% 2.15/1.26  Abstraction          : 0.01
% 2.15/1.26  MUC search           : 0.00
% 2.15/1.26  Cooper               : 0.00
% 2.15/1.26  Total                : 0.53
% 2.15/1.26  Index Insertion      : 0.00
% 2.15/1.26  Index Deletion       : 0.00
% 2.15/1.26  Index Matching       : 0.00
% 2.15/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
