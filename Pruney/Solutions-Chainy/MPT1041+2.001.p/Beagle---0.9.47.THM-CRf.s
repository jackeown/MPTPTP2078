%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:03 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   51 (  81 expanded)
%              Number of leaves         :   24 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 234 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r1_partfun1(B,C)
             => r2_hidden(C,k5_partfun1(A,A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( D = k5_partfun1(A,B,C)
        <=> ! [E] :
              ( r2_hidden(E,D)
            <=> ? [F] :
                  ( v1_funct_1(F)
                  & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(A,B)))
                  & F = E
                  & v1_partfun1(F,A)
                  & r1_partfun1(C,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

tff(c_44,plain,(
    ~ r2_hidden('#skF_7',k5_partfun1('#skF_5','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_46,plain,(
    r1_partfun1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_52,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_57,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_partfun1(C_52,A_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_57])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_50,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_68,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_partfun1(C_55,A_56)
      | ~ v1_funct_2(C_55,A_56,B_57)
      | ~ v1_funct_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57)))
      | v1_xboole_0(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_71,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_7')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_68])).

tff(c_77,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_71])).

tff(c_78,plain,(
    v1_partfun1('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_77])).

tff(c_208,plain,(
    ! [F_104,A_105,B_106,C_107] :
      ( r2_hidden(F_104,k5_partfun1(A_105,B_106,C_107))
      | ~ r1_partfun1(C_107,F_104)
      | ~ v1_partfun1(F_104,A_105)
      | ~ m1_subset_1(F_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ v1_funct_1(F_104)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106)))
      | ~ v1_funct_1(C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_212,plain,(
    ! [C_107] :
      ( r2_hidden('#skF_7',k5_partfun1('#skF_5','#skF_5',C_107))
      | ~ r1_partfun1(C_107,'#skF_7')
      | ~ v1_partfun1('#skF_7','#skF_5')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
      | ~ v1_funct_1(C_107) ) ),
    inference(resolution,[status(thm)],[c_48,c_208])).

tff(c_222,plain,(
    ! [C_108] :
      ( r2_hidden('#skF_7',k5_partfun1('#skF_5','#skF_5',C_108))
      | ~ r1_partfun1(C_108,'#skF_7')
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
      | ~ v1_funct_1(C_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_78,c_212])).

tff(c_232,plain,
    ( r2_hidden('#skF_7',k5_partfun1('#skF_5','#skF_5','#skF_6'))
    | ~ r1_partfun1('#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_222])).

tff(c_239,plain,(
    r2_hidden('#skF_7',k5_partfun1('#skF_5','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_232])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_239])).

tff(c_242,plain,(
    v1_partfun1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_387,plain,(
    ! [F_157,A_158,B_159,C_160] :
      ( r2_hidden(F_157,k5_partfun1(A_158,B_159,C_160))
      | ~ r1_partfun1(C_160,F_157)
      | ~ v1_partfun1(F_157,A_158)
      | ~ m1_subset_1(F_157,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ v1_funct_1(F_157)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159)))
      | ~ v1_funct_1(C_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_389,plain,(
    ! [C_160] :
      ( r2_hidden('#skF_7',k5_partfun1('#skF_5','#skF_5',C_160))
      | ~ r1_partfun1(C_160,'#skF_7')
      | ~ v1_partfun1('#skF_7','#skF_5')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
      | ~ v1_funct_1(C_160) ) ),
    inference(resolution,[status(thm)],[c_48,c_387])).

tff(c_398,plain,(
    ! [C_161] :
      ( r2_hidden('#skF_7',k5_partfun1('#skF_5','#skF_5',C_161))
      | ~ r1_partfun1(C_161,'#skF_7')
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
      | ~ v1_funct_1(C_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_242,c_389])).

tff(c_404,plain,
    ( r2_hidden('#skF_7',k5_partfun1('#skF_5','#skF_5','#skF_6'))
    | ~ r1_partfun1('#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_398])).

tff(c_410,plain,(
    r2_hidden('#skF_7',k5_partfun1('#skF_5','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_404])).

tff(c_412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_410])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:49:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.37  
% 2.76/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.38  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 2.76/1.38  
% 2.76/1.38  %Foreground sorts:
% 2.76/1.38  
% 2.76/1.38  
% 2.76/1.38  %Background operators:
% 2.76/1.38  
% 2.76/1.38  
% 2.76/1.38  %Foreground operators:
% 2.76/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.76/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 2.76/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.76/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.76/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.76/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.76/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.76/1.38  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.76/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.76/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.76/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.76/1.38  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 2.76/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.38  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.76/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.38  
% 2.76/1.39  tff(f_83, negated_conjecture, ~(![A, B]: ((v1_funct_1(B) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_partfun1(B, C) => r2_hidden(C, k5_partfun1(A, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t156_funct_2)).
% 2.76/1.39  tff(f_32, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 2.76/1.39  tff(f_46, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.76/1.39  tff(f_67, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((D = k5_partfun1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> (?[F]: ((((v1_funct_1(F) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & (F = E)) & v1_partfun1(F, A)) & r1_partfun1(C, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 2.76/1.39  tff(c_44, plain, (~r2_hidden('#skF_7', k5_partfun1('#skF_5', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.76/1.39  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.76/1.39  tff(c_46, plain, (r1_partfun1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.76/1.39  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.76/1.39  tff(c_52, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.76/1.39  tff(c_48, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.76/1.39  tff(c_57, plain, (![C_52, A_53, B_54]: (v1_partfun1(C_52, A_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.39  tff(c_64, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_48, c_57])).
% 2.76/1.39  tff(c_66, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_64])).
% 2.76/1.39  tff(c_50, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.76/1.39  tff(c_68, plain, (![C_55, A_56, B_57]: (v1_partfun1(C_55, A_56) | ~v1_funct_2(C_55, A_56, B_57) | ~v1_funct_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))) | v1_xboole_0(B_57))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.76/1.39  tff(c_71, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_7') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_48, c_68])).
% 2.76/1.39  tff(c_77, plain, (v1_partfun1('#skF_7', '#skF_5') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_71])).
% 2.76/1.39  tff(c_78, plain, (v1_partfun1('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_66, c_77])).
% 2.76/1.39  tff(c_208, plain, (![F_104, A_105, B_106, C_107]: (r2_hidden(F_104, k5_partfun1(A_105, B_106, C_107)) | ~r1_partfun1(C_107, F_104) | ~v1_partfun1(F_104, A_105) | ~m1_subset_1(F_104, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))) | ~v1_funct_1(F_104) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))) | ~v1_funct_1(C_107))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.76/1.39  tff(c_212, plain, (![C_107]: (r2_hidden('#skF_7', k5_partfun1('#skF_5', '#skF_5', C_107)) | ~r1_partfun1(C_107, '#skF_7') | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_1('#skF_7') | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_1(C_107))), inference(resolution, [status(thm)], [c_48, c_208])).
% 2.76/1.39  tff(c_222, plain, (![C_108]: (r2_hidden('#skF_7', k5_partfun1('#skF_5', '#skF_5', C_108)) | ~r1_partfun1(C_108, '#skF_7') | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_1(C_108))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_78, c_212])).
% 2.76/1.39  tff(c_232, plain, (r2_hidden('#skF_7', k5_partfun1('#skF_5', '#skF_5', '#skF_6')) | ~r1_partfun1('#skF_6', '#skF_7') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_222])).
% 2.76/1.39  tff(c_239, plain, (r2_hidden('#skF_7', k5_partfun1('#skF_5', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_232])).
% 2.76/1.39  tff(c_241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_239])).
% 2.76/1.39  tff(c_242, plain, (v1_partfun1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_64])).
% 2.76/1.39  tff(c_387, plain, (![F_157, A_158, B_159, C_160]: (r2_hidden(F_157, k5_partfun1(A_158, B_159, C_160)) | ~r1_partfun1(C_160, F_157) | ~v1_partfun1(F_157, A_158) | ~m1_subset_1(F_157, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~v1_funct_1(F_157) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))) | ~v1_funct_1(C_160))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.76/1.39  tff(c_389, plain, (![C_160]: (r2_hidden('#skF_7', k5_partfun1('#skF_5', '#skF_5', C_160)) | ~r1_partfun1(C_160, '#skF_7') | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_1('#skF_7') | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_1(C_160))), inference(resolution, [status(thm)], [c_48, c_387])).
% 2.76/1.39  tff(c_398, plain, (![C_161]: (r2_hidden('#skF_7', k5_partfun1('#skF_5', '#skF_5', C_161)) | ~r1_partfun1(C_161, '#skF_7') | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_1(C_161))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_242, c_389])).
% 2.76/1.39  tff(c_404, plain, (r2_hidden('#skF_7', k5_partfun1('#skF_5', '#skF_5', '#skF_6')) | ~r1_partfun1('#skF_6', '#skF_7') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_398])).
% 2.76/1.39  tff(c_410, plain, (r2_hidden('#skF_7', k5_partfun1('#skF_5', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_404])).
% 2.76/1.39  tff(c_412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_410])).
% 2.76/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.39  
% 2.76/1.39  Inference rules
% 2.76/1.39  ----------------------
% 2.76/1.39  #Ref     : 0
% 2.76/1.39  #Sup     : 65
% 2.76/1.39  #Fact    : 0
% 2.76/1.39  #Define  : 0
% 2.76/1.39  #Split   : 3
% 2.76/1.39  #Chain   : 0
% 2.76/1.39  #Close   : 0
% 2.76/1.39  
% 2.76/1.39  Ordering : KBO
% 2.76/1.39  
% 2.76/1.39  Simplification rules
% 2.76/1.39  ----------------------
% 2.76/1.39  #Subsume      : 3
% 2.76/1.39  #Demod        : 48
% 2.76/1.39  #Tautology    : 6
% 2.76/1.39  #SimpNegUnit  : 4
% 2.76/1.39  #BackRed      : 0
% 2.76/1.39  
% 2.76/1.39  #Partial instantiations: 0
% 2.76/1.39  #Strategies tried      : 1
% 2.76/1.39  
% 2.76/1.39  Timing (in seconds)
% 2.76/1.39  ----------------------
% 2.76/1.39  Preprocessing        : 0.33
% 2.76/1.39  Parsing              : 0.16
% 2.76/1.39  CNF conversion       : 0.03
% 2.76/1.39  Main loop            : 0.29
% 2.76/1.39  Inferencing          : 0.12
% 2.76/1.39  Reduction            : 0.08
% 2.76/1.39  Demodulation         : 0.06
% 2.76/1.39  BG Simplification    : 0.02
% 2.76/1.39  Subsumption          : 0.05
% 2.76/1.39  Abstraction          : 0.02
% 2.76/1.39  MUC search           : 0.00
% 2.76/1.39  Cooper               : 0.00
% 2.76/1.39  Total                : 0.65
% 2.76/1.39  Index Insertion      : 0.00
% 2.76/1.39  Index Deletion       : 0.00
% 2.76/1.39  Index Matching       : 0.00
% 2.76/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
