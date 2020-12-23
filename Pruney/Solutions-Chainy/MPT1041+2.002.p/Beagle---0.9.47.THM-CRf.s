%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:03 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 106 expanded)
%              Number of leaves         :   23 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :   80 ( 344 expanded)
%              Number of equality atoms :    8 (  32 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r1_partfun1(B,C)
             => r2_hidden(C,k5_partfun1(A,A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_46,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

tff(c_42,plain,(
    ~ r2_hidden('#skF_7',k5_partfun1('#skF_5','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44,plain,(
    r1_partfun1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_50,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_48,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_56,plain,(
    ! [B_49,C_50,A_51] :
      ( k1_xboole_0 = B_49
      | v1_partfun1(C_50,A_51)
      | ~ v1_funct_2(C_50,A_51,B_49)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_49)))
      | ~ v1_funct_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_59,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_56])).

tff(c_65,plain,
    ( k1_xboole_0 = '#skF_5'
    | v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_59])).

tff(c_69,plain,(
    v1_partfun1('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_171,plain,(
    ! [F_94,A_95,B_96,C_97] :
      ( r2_hidden(F_94,k5_partfun1(A_95,B_96,C_97))
      | ~ r1_partfun1(C_97,F_94)
      | ~ v1_partfun1(F_94,A_95)
      | ~ m1_subset_1(F_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_1(F_94)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ v1_funct_1(C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_173,plain,(
    ! [C_97] :
      ( r2_hidden('#skF_7',k5_partfun1('#skF_5','#skF_5',C_97))
      | ~ r1_partfun1(C_97,'#skF_7')
      | ~ v1_partfun1('#skF_7','#skF_5')
      | ~ v1_funct_1('#skF_7')
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
      | ~ v1_funct_1(C_97) ) ),
    inference(resolution,[status(thm)],[c_46,c_171])).

tff(c_182,plain,(
    ! [C_98] :
      ( r2_hidden('#skF_7',k5_partfun1('#skF_5','#skF_5',C_98))
      | ~ r1_partfun1(C_98,'#skF_7')
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
      | ~ v1_funct_1(C_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_69,c_173])).

tff(c_188,plain,
    ( r2_hidden('#skF_7',k5_partfun1('#skF_5','#skF_5','#skF_6'))
    | ~ r1_partfun1('#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_182])).

tff(c_194,plain,(
    r2_hidden('#skF_7',k5_partfun1('#skF_5','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_44,c_188])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_194])).

tff(c_198,plain,(
    ~ v1_partfun1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_197,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_38,plain,(
    ! [C_45,B_44] :
      ( v1_partfun1(C_45,k1_xboole_0)
      | ~ v1_funct_2(C_45,k1_xboole_0,B_44)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_44)))
      | ~ v1_funct_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_207,plain,(
    ! [C_103,B_104] :
      ( v1_partfun1(C_103,'#skF_5')
      | ~ v1_funct_2(C_103,'#skF_5',B_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_104)))
      | ~ v1_funct_1(C_103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_197,c_197,c_38])).

tff(c_210,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_207])).

tff(c_216,plain,(
    v1_partfun1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_210])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:47:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.33  
% 2.16/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.34  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 2.16/1.34  
% 2.16/1.34  %Foreground sorts:
% 2.16/1.34  
% 2.16/1.34  
% 2.16/1.34  %Background operators:
% 2.16/1.34  
% 2.16/1.34  
% 2.16/1.34  %Foreground operators:
% 2.16/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.16/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.34  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 2.16/1.34  tff('#skF_7', type, '#skF_7': $i).
% 2.16/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.16/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.16/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.16/1.34  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.16/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.16/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.16/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.16/1.34  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 2.16/1.34  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 2.16/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.34  
% 2.16/1.35  tff(f_79, negated_conjecture, ~(![A, B]: ((v1_funct_1(B) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_partfun1(B, C) => r2_hidden(C, k5_partfun1(A, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_funct_2)).
% 2.16/1.35  tff(f_63, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 2.16/1.35  tff(f_46, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((D = k5_partfun1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> (?[F]: ((((v1_funct_1(F) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & (F = E)) & v1_partfun1(F, A)) & r1_partfun1(C, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_partfun1)).
% 2.16/1.35  tff(c_42, plain, (~r2_hidden('#skF_7', k5_partfun1('#skF_5', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.16/1.35  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.16/1.35  tff(c_44, plain, (r1_partfun1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.16/1.35  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.16/1.35  tff(c_50, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.16/1.35  tff(c_48, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.16/1.35  tff(c_46, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.16/1.35  tff(c_56, plain, (![B_49, C_50, A_51]: (k1_xboole_0=B_49 | v1_partfun1(C_50, A_51) | ~v1_funct_2(C_50, A_51, B_49) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_49))) | ~v1_funct_1(C_50))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.16/1.35  tff(c_59, plain, (k1_xboole_0='#skF_5' | v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_46, c_56])).
% 2.16/1.35  tff(c_65, plain, (k1_xboole_0='#skF_5' | v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_59])).
% 2.16/1.35  tff(c_69, plain, (v1_partfun1('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_65])).
% 2.16/1.35  tff(c_171, plain, (![F_94, A_95, B_96, C_97]: (r2_hidden(F_94, k5_partfun1(A_95, B_96, C_97)) | ~r1_partfun1(C_97, F_94) | ~v1_partfun1(F_94, A_95) | ~m1_subset_1(F_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_1(F_94) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~v1_funct_1(C_97))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.16/1.35  tff(c_173, plain, (![C_97]: (r2_hidden('#skF_7', k5_partfun1('#skF_5', '#skF_5', C_97)) | ~r1_partfun1(C_97, '#skF_7') | ~v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_1('#skF_7') | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_1(C_97))), inference(resolution, [status(thm)], [c_46, c_171])).
% 2.16/1.35  tff(c_182, plain, (![C_98]: (r2_hidden('#skF_7', k5_partfun1('#skF_5', '#skF_5', C_98)) | ~r1_partfun1(C_98, '#skF_7') | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_1(C_98))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_69, c_173])).
% 2.16/1.35  tff(c_188, plain, (r2_hidden('#skF_7', k5_partfun1('#skF_5', '#skF_5', '#skF_6')) | ~r1_partfun1('#skF_6', '#skF_7') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_182])).
% 2.16/1.35  tff(c_194, plain, (r2_hidden('#skF_7', k5_partfun1('#skF_5', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_44, c_188])).
% 2.16/1.35  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_194])).
% 2.16/1.35  tff(c_198, plain, (~v1_partfun1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_65])).
% 2.16/1.35  tff(c_197, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_65])).
% 2.16/1.35  tff(c_38, plain, (![C_45, B_44]: (v1_partfun1(C_45, k1_xboole_0) | ~v1_funct_2(C_45, k1_xboole_0, B_44) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_44))) | ~v1_funct_1(C_45))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.16/1.35  tff(c_207, plain, (![C_103, B_104]: (v1_partfun1(C_103, '#skF_5') | ~v1_funct_2(C_103, '#skF_5', B_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_104))) | ~v1_funct_1(C_103))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_197, c_197, c_38])).
% 2.16/1.35  tff(c_210, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_funct_2('#skF_7', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_46, c_207])).
% 2.16/1.35  tff(c_216, plain, (v1_partfun1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_210])).
% 2.16/1.35  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_198, c_216])).
% 2.16/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.35  
% 2.16/1.35  Inference rules
% 2.16/1.35  ----------------------
% 2.16/1.35  #Ref     : 0
% 2.16/1.35  #Sup     : 28
% 2.16/1.35  #Fact    : 0
% 2.16/1.35  #Define  : 0
% 2.16/1.35  #Split   : 2
% 2.16/1.35  #Chain   : 0
% 2.16/1.35  #Close   : 0
% 2.16/1.35  
% 2.16/1.35  Ordering : KBO
% 2.16/1.35  
% 2.16/1.35  Simplification rules
% 2.16/1.35  ----------------------
% 2.16/1.35  #Subsume      : 0
% 2.16/1.35  #Demod        : 26
% 2.16/1.35  #Tautology    : 3
% 2.16/1.35  #SimpNegUnit  : 2
% 2.16/1.35  #BackRed      : 2
% 2.16/1.35  
% 2.16/1.35  #Partial instantiations: 0
% 2.16/1.35  #Strategies tried      : 1
% 2.16/1.35  
% 2.16/1.35  Timing (in seconds)
% 2.16/1.35  ----------------------
% 2.42/1.35  Preprocessing        : 0.32
% 2.42/1.35  Parsing              : 0.16
% 2.42/1.35  CNF conversion       : 0.03
% 2.42/1.35  Main loop            : 0.24
% 2.42/1.35  Inferencing          : 0.09
% 2.42/1.35  Reduction            : 0.08
% 2.42/1.35  Demodulation         : 0.05
% 2.42/1.35  BG Simplification    : 0.02
% 2.42/1.35  Subsumption          : 0.04
% 2.42/1.35  Abstraction          : 0.02
% 2.42/1.35  MUC search           : 0.00
% 2.42/1.35  Cooper               : 0.00
% 2.42/1.35  Total                : 0.61
% 2.42/1.35  Index Insertion      : 0.00
% 2.42/1.35  Index Deletion       : 0.00
% 2.42/1.35  Index Matching       : 0.00
% 2.42/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
