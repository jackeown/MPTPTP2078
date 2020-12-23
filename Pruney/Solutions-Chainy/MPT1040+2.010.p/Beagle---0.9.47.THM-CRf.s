%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:03 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 133 expanded)
%              Number of leaves         :   24 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 460 expanded)
%              Number of equality atoms :   15 ( 122 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_hidden(D,k5_partfun1(A,B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_partfun1)).

tff(c_42,plain,(
    ~ r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_56,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_46,plain,(
    r1_partfun1('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_52,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_44,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_57,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_48,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_59,plain,(
    ! [B_49,C_50,A_51] :
      ( k1_xboole_0 = B_49
      | v1_partfun1(C_50,A_51)
      | ~ v1_funct_2(C_50,A_51,B_49)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_49)))
      | ~ v1_funct_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_6'
    | v1_partfun1('#skF_8','#skF_5')
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_59])).

tff(c_68,plain,
    ( k1_xboole_0 = '#skF_6'
    | v1_partfun1('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_62])).

tff(c_69,plain,(
    v1_partfun1('#skF_8','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_68])).

tff(c_231,plain,(
    ! [F_101,A_102,B_103,C_104] :
      ( r2_hidden(F_101,k5_partfun1(A_102,B_103,C_104))
      | ~ r1_partfun1(C_104,F_101)
      | ~ v1_partfun1(F_101,A_102)
      | ~ m1_subset_1(F_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103)))
      | ~ v1_funct_1(F_101)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103)))
      | ~ v1_funct_1(C_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_235,plain,(
    ! [C_104] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6',C_104))
      | ~ r1_partfun1(C_104,'#skF_8')
      | ~ v1_partfun1('#skF_8','#skF_5')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_104) ) ),
    inference(resolution,[status(thm)],[c_48,c_231])).

tff(c_277,plain,(
    ! [C_109] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6',C_109))
      | ~ r1_partfun1(C_109,'#skF_8')
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | ~ v1_funct_1(C_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_69,c_235])).

tff(c_291,plain,
    ( r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7'))
    | ~ r1_partfun1('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_277])).

tff(c_299,plain,(
    r2_hidden('#skF_8',k5_partfun1('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_291])).

tff(c_301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_299])).

tff(c_303,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_302,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_308,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_302])).

tff(c_319,plain,(
    ~ r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_42])).

tff(c_320,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_54])).

tff(c_314,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_50])).

tff(c_313,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_48])).

tff(c_38,plain,(
    ! [C_45,B_44] :
      ( v1_partfun1(C_45,k1_xboole_0)
      | ~ v1_funct_2(C_45,k1_xboole_0,B_44)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_44)))
      | ~ v1_funct_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_322,plain,(
    ! [C_110,B_111] :
      ( v1_partfun1(C_110,'#skF_6')
      | ~ v1_funct_2(C_110,'#skF_6',B_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_111)))
      | ~ v1_funct_1(C_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_303,c_303,c_38])).

tff(c_328,plain,
    ( v1_partfun1('#skF_8','#skF_6')
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_6')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_313,c_322])).

tff(c_334,plain,(
    v1_partfun1('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_314,c_328])).

tff(c_507,plain,(
    ! [F_163,A_164,B_165,C_166] :
      ( r2_hidden(F_163,k5_partfun1(A_164,B_165,C_166))
      | ~ r1_partfun1(C_166,F_163)
      | ~ v1_partfun1(F_163,A_164)
      | ~ m1_subset_1(F_163,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165)))
      | ~ v1_funct_1(F_163)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165)))
      | ~ v1_funct_1(C_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_511,plain,(
    ! [C_166] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6',C_166))
      | ~ r1_partfun1(C_166,'#skF_8')
      | ~ v1_partfun1('#skF_8','#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v1_funct_1(C_166) ) ),
    inference(resolution,[status(thm)],[c_313,c_507])).

tff(c_518,plain,(
    ! [C_167] :
      ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6',C_167))
      | ~ r1_partfun1(C_167,'#skF_8')
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
      | ~ v1_funct_1(C_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_334,c_511])).

tff(c_521,plain,
    ( r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6','#skF_7'))
    | ~ r1_partfun1('#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_320,c_518])).

tff(c_527,plain,(
    r2_hidden('#skF_8',k5_partfun1('#skF_6','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_46,c_521])).

tff(c_529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_319,c_527])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:59:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.47  
% 3.01/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.47  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_partfun1 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 3.01/1.47  
% 3.01/1.47  %Foreground sorts:
% 3.01/1.47  
% 3.01/1.47  
% 3.01/1.47  %Background operators:
% 3.01/1.47  
% 3.01/1.47  
% 3.01/1.47  %Foreground operators:
% 3.01/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.01/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.01/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.01/1.47  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 3.01/1.47  tff('#skF_7', type, '#skF_7': $i).
% 3.01/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.01/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.01/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.01/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.01/1.47  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.01/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.01/1.47  tff('#skF_8', type, '#skF_8': $i).
% 3.01/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.01/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.01/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.01/1.47  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 3.01/1.47  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 3.01/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.01/1.47  
% 3.01/1.48  tff(f_84, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_hidden(D, k5_partfun1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t155_funct_2)).
% 3.01/1.48  tff(f_63, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 3.01/1.48  tff(f_46, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((D = k5_partfun1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> (?[F]: ((((v1_funct_1(F) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & (F = E)) & v1_partfun1(F, A)) & r1_partfun1(C, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_partfun1)).
% 3.01/1.48  tff(c_42, plain, (~r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.01/1.48  tff(c_56, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.01/1.48  tff(c_46, plain, (r1_partfun1('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.01/1.48  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.01/1.48  tff(c_52, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.01/1.48  tff(c_44, plain, (k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.01/1.48  tff(c_57, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_44])).
% 3.01/1.48  tff(c_50, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.01/1.48  tff(c_48, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.01/1.48  tff(c_59, plain, (![B_49, C_50, A_51]: (k1_xboole_0=B_49 | v1_partfun1(C_50, A_51) | ~v1_funct_2(C_50, A_51, B_49) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_49))) | ~v1_funct_1(C_50))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.01/1.48  tff(c_62, plain, (k1_xboole_0='#skF_6' | v1_partfun1('#skF_8', '#skF_5') | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_59])).
% 3.01/1.48  tff(c_68, plain, (k1_xboole_0='#skF_6' | v1_partfun1('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_62])).
% 3.01/1.48  tff(c_69, plain, (v1_partfun1('#skF_8', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_57, c_68])).
% 3.01/1.48  tff(c_231, plain, (![F_101, A_102, B_103, C_104]: (r2_hidden(F_101, k5_partfun1(A_102, B_103, C_104)) | ~r1_partfun1(C_104, F_101) | ~v1_partfun1(F_101, A_102) | ~m1_subset_1(F_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))) | ~v1_funct_1(F_101) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))) | ~v1_funct_1(C_104))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.01/1.48  tff(c_235, plain, (![C_104]: (r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', C_104)) | ~r1_partfun1(C_104, '#skF_8') | ~v1_partfun1('#skF_8', '#skF_5') | ~v1_funct_1('#skF_8') | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_104))), inference(resolution, [status(thm)], [c_48, c_231])).
% 3.01/1.48  tff(c_277, plain, (![C_109]: (r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', C_109)) | ~r1_partfun1(C_109, '#skF_8') | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | ~v1_funct_1(C_109))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_69, c_235])).
% 3.01/1.48  tff(c_291, plain, (r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7')) | ~r1_partfun1('#skF_7', '#skF_8') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_54, c_277])).
% 3.01/1.48  tff(c_299, plain, (r2_hidden('#skF_8', k5_partfun1('#skF_5', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_291])).
% 3.01/1.48  tff(c_301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_299])).
% 3.01/1.48  tff(c_303, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_44])).
% 3.01/1.48  tff(c_302, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_44])).
% 3.01/1.48  tff(c_308, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_303, c_302])).
% 3.01/1.48  tff(c_319, plain, (~r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_42])).
% 3.01/1.48  tff(c_320, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_54])).
% 3.01/1.48  tff(c_314, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_308, c_50])).
% 3.01/1.48  tff(c_313, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_48])).
% 3.01/1.48  tff(c_38, plain, (![C_45, B_44]: (v1_partfun1(C_45, k1_xboole_0) | ~v1_funct_2(C_45, k1_xboole_0, B_44) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_44))) | ~v1_funct_1(C_45))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.01/1.48  tff(c_322, plain, (![C_110, B_111]: (v1_partfun1(C_110, '#skF_6') | ~v1_funct_2(C_110, '#skF_6', B_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_111))) | ~v1_funct_1(C_110))), inference(demodulation, [status(thm), theory('equality')], [c_303, c_303, c_303, c_38])).
% 3.01/1.48  tff(c_328, plain, (v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_2('#skF_8', '#skF_6', '#skF_6') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_313, c_322])).
% 3.01/1.48  tff(c_334, plain, (v1_partfun1('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_314, c_328])).
% 3.01/1.48  tff(c_507, plain, (![F_163, A_164, B_165, C_166]: (r2_hidden(F_163, k5_partfun1(A_164, B_165, C_166)) | ~r1_partfun1(C_166, F_163) | ~v1_partfun1(F_163, A_164) | ~m1_subset_1(F_163, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))) | ~v1_funct_1(F_163) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))) | ~v1_funct_1(C_166))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.01/1.48  tff(c_511, plain, (![C_166]: (r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', C_166)) | ~r1_partfun1(C_166, '#skF_8') | ~v1_partfun1('#skF_8', '#skF_6') | ~v1_funct_1('#skF_8') | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6'))) | ~v1_funct_1(C_166))), inference(resolution, [status(thm)], [c_313, c_507])).
% 3.01/1.48  tff(c_518, plain, (![C_167]: (r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', C_167)) | ~r1_partfun1(C_167, '#skF_8') | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6'))) | ~v1_funct_1(C_167))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_334, c_511])).
% 3.01/1.48  tff(c_521, plain, (r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', '#skF_7')) | ~r1_partfun1('#skF_7', '#skF_8') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_320, c_518])).
% 3.01/1.48  tff(c_527, plain, (r2_hidden('#skF_8', k5_partfun1('#skF_6', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_46, c_521])).
% 3.01/1.48  tff(c_529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_319, c_527])).
% 3.01/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.48  
% 3.01/1.48  Inference rules
% 3.01/1.48  ----------------------
% 3.01/1.48  #Ref     : 0
% 3.01/1.48  #Sup     : 94
% 3.01/1.48  #Fact    : 0
% 3.01/1.48  #Define  : 0
% 3.01/1.48  #Split   : 3
% 3.01/1.48  #Chain   : 0
% 3.01/1.49  #Close   : 0
% 3.01/1.49  
% 3.01/1.49  Ordering : KBO
% 3.01/1.49  
% 3.01/1.49  Simplification rules
% 3.01/1.49  ----------------------
% 3.01/1.49  #Subsume      : 5
% 3.01/1.49  #Demod        : 62
% 3.01/1.49  #Tautology    : 16
% 3.01/1.49  #SimpNegUnit  : 4
% 3.01/1.49  #BackRed      : 3
% 3.01/1.49  
% 3.01/1.49  #Partial instantiations: 0
% 3.01/1.49  #Strategies tried      : 1
% 3.01/1.49  
% 3.01/1.49  Timing (in seconds)
% 3.01/1.49  ----------------------
% 3.01/1.49  Preprocessing        : 0.33
% 3.01/1.49  Parsing              : 0.17
% 3.01/1.49  CNF conversion       : 0.03
% 3.01/1.49  Main loop            : 0.34
% 3.01/1.49  Inferencing          : 0.13
% 3.01/1.49  Reduction            : 0.10
% 3.01/1.49  Demodulation         : 0.07
% 3.01/1.49  BG Simplification    : 0.02
% 3.01/1.49  Subsumption          : 0.05
% 3.01/1.49  Abstraction          : 0.02
% 3.01/1.49  MUC search           : 0.00
% 3.01/1.49  Cooper               : 0.00
% 3.01/1.49  Total                : 0.70
% 3.01/1.49  Index Insertion      : 0.00
% 3.01/1.49  Index Deletion       : 0.00
% 3.01/1.49  Index Matching       : 0.00
% 3.01/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
