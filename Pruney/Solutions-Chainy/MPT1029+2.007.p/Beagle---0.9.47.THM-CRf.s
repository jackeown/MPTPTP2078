%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:49 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 228 expanded)
%              Number of leaves         :   29 (  83 expanded)
%              Depth                    :   11
%              Number of atoms          :   89 ( 598 expanded)
%              Number of equality atoms :   22 ( 229 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v8_relat_2 > v4_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_2 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v3_relat_2,type,(
    v3_relat_2: $i > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_76,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
      & v1_relat_1(B)
      & v4_relat_1(B,A)
      & v5_relat_1(B,A)
      & v1_relat_2(B)
      & v3_relat_2(B)
      & v4_relat_2(B)
      & v8_relat_2(B)
      & v1_partfun1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_partfun1)).

tff(c_38,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_36,plain,(
    ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_42,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_158,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_partfun1(C_29,A_30)
      | ~ v1_funct_2(C_29,A_30,B_31)
      | ~ v1_funct_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | v1_xboole_0(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_164,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_158])).

tff(c_175,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_164])).

tff(c_176,plain,(
    v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_175])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_180,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_176,c_4])).

tff(c_184,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_180])).

tff(c_186,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_185,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_192,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_185])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_187,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_2])).

tff(c_203,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_187])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_205,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_3',B_3) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_186,c_10])).

tff(c_238,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_192,c_46])).

tff(c_249,plain,(
    ! [B_39,A_40] :
      ( v1_xboole_0(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_40))
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_258,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_238,c_249])).

tff(c_265,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_258])).

tff(c_213,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_4])).

tff(c_281,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_265,c_213])).

tff(c_198,plain,(
    ~ v1_partfun1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_36])).

tff(c_289,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_198])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_221,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_186,c_8])).

tff(c_239,plain,(
    ! [A_38] : m1_subset_1('#skF_1'(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_243,plain,(
    m1_subset_1('#skF_1'('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_239])).

tff(c_252,plain,
    ( v1_xboole_0('#skF_1'('#skF_3'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_243,c_249])).

tff(c_261,plain,(
    v1_xboole_0('#skF_1'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_252])).

tff(c_306,plain,(
    v1_xboole_0('#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_261])).

tff(c_318,plain,(
    ! [A_44] :
      ( A_44 = '#skF_4'
      | ~ v1_xboole_0(A_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_213])).

tff(c_325,plain,(
    '#skF_1'('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_306,c_318])).

tff(c_18,plain,(
    ! [A_11] : v1_partfun1('#skF_1'(A_11),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_342,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_18])).

tff(c_357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_342])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:54:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.26  
% 2.37/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.27  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v8_relat_2 > v4_relat_2 > v3_relat_2 > v1_xboole_0 > v1_relat_2 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.37/1.27  
% 2.37/1.27  %Foreground sorts:
% 2.37/1.27  
% 2.37/1.27  
% 2.37/1.27  %Background operators:
% 2.37/1.27  
% 2.37/1.27  
% 2.37/1.27  %Foreground operators:
% 2.37/1.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.37/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.37/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.27  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 2.37/1.27  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 2.37/1.27  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 2.37/1.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.37/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.27  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.37/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.37/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.37/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.37/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.37/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.27  tff(v3_relat_2, type, v3_relat_2: $i > $o).
% 2.37/1.27  
% 2.37/1.28  tff(f_94, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 2.37/1.28  tff(f_57, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.37/1.28  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.37/1.28  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.37/1.28  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.37/1.28  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.37/1.28  tff(f_76, axiom, (![A]: (?[B]: ((((((((m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) & v1_relat_1(B)) & v4_relat_1(B, A)) & v5_relat_1(B, A)) & v1_relat_2(B)) & v3_relat_2(B)) & v4_relat_2(B)) & v8_relat_2(B)) & v1_partfun1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_partfun1)).
% 2.37/1.28  tff(c_38, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.37/1.28  tff(c_56, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_38])).
% 2.37/1.28  tff(c_36, plain, (~v1_partfun1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.37/1.28  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.37/1.28  tff(c_42, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.37/1.28  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.37/1.28  tff(c_158, plain, (![C_29, A_30, B_31]: (v1_partfun1(C_29, A_30) | ~v1_funct_2(C_29, A_30, B_31) | ~v1_funct_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | v1_xboole_0(B_31))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.37/1.28  tff(c_164, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_158])).
% 2.37/1.28  tff(c_175, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_164])).
% 2.37/1.28  tff(c_176, plain, (v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_36, c_175])).
% 2.37/1.28  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.37/1.28  tff(c_180, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_176, c_4])).
% 2.37/1.28  tff(c_184, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_180])).
% 2.37/1.28  tff(c_186, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 2.37/1.28  tff(c_185, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_38])).
% 2.37/1.28  tff(c_192, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_186, c_185])).
% 2.37/1.28  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.37/1.28  tff(c_187, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_2])).
% 2.37/1.28  tff(c_203, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_192, c_187])).
% 2.37/1.28  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.37/1.28  tff(c_205, plain, (![B_3]: (k2_zfmisc_1('#skF_3', B_3)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_186, c_10])).
% 2.37/1.28  tff(c_238, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_192, c_46])).
% 2.37/1.28  tff(c_249, plain, (![B_39, A_40]: (v1_xboole_0(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_40)) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.37/1.28  tff(c_258, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_238, c_249])).
% 2.37/1.28  tff(c_265, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_258])).
% 2.37/1.28  tff(c_213, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_4])).
% 2.37/1.28  tff(c_281, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_265, c_213])).
% 2.37/1.28  tff(c_198, plain, (~v1_partfun1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_192, c_36])).
% 2.37/1.28  tff(c_289, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_281, c_198])).
% 2.37/1.28  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.37/1.28  tff(c_221, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_186, c_8])).
% 2.37/1.28  tff(c_239, plain, (![A_38]: (m1_subset_1('#skF_1'(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.37/1.28  tff(c_243, plain, (m1_subset_1('#skF_1'('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_221, c_239])).
% 2.37/1.28  tff(c_252, plain, (v1_xboole_0('#skF_1'('#skF_3')) | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_243, c_249])).
% 2.37/1.28  tff(c_261, plain, (v1_xboole_0('#skF_1'('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_252])).
% 2.37/1.28  tff(c_306, plain, (v1_xboole_0('#skF_1'('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_261])).
% 2.37/1.28  tff(c_318, plain, (![A_44]: (A_44='#skF_4' | ~v1_xboole_0(A_44))), inference(demodulation, [status(thm), theory('equality')], [c_281, c_213])).
% 2.37/1.28  tff(c_325, plain, ('#skF_1'('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_306, c_318])).
% 2.37/1.28  tff(c_18, plain, (![A_11]: (v1_partfun1('#skF_1'(A_11), A_11))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.37/1.28  tff(c_342, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_325, c_18])).
% 2.37/1.28  tff(c_357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_289, c_342])).
% 2.37/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.28  
% 2.37/1.28  Inference rules
% 2.37/1.28  ----------------------
% 2.37/1.28  #Ref     : 0
% 2.37/1.28  #Sup     : 74
% 2.37/1.28  #Fact    : 0
% 2.37/1.28  #Define  : 0
% 2.37/1.28  #Split   : 1
% 2.37/1.28  #Chain   : 0
% 2.37/1.28  #Close   : 0
% 2.37/1.28  
% 2.37/1.28  Ordering : KBO
% 2.37/1.28  
% 2.37/1.28  Simplification rules
% 2.37/1.28  ----------------------
% 2.37/1.28  #Subsume      : 0
% 2.37/1.28  #Demod        : 52
% 2.37/1.28  #Tautology    : 46
% 2.37/1.28  #SimpNegUnit  : 3
% 2.37/1.28  #BackRed      : 18
% 2.37/1.28  
% 2.37/1.28  #Partial instantiations: 0
% 2.37/1.28  #Strategies tried      : 1
% 2.37/1.28  
% 2.37/1.28  Timing (in seconds)
% 2.37/1.28  ----------------------
% 2.37/1.28  Preprocessing        : 0.30
% 2.37/1.28  Parsing              : 0.16
% 2.37/1.28  CNF conversion       : 0.02
% 2.37/1.29  Main loop            : 0.20
% 2.37/1.29  Inferencing          : 0.07
% 2.37/1.29  Reduction            : 0.07
% 2.37/1.29  Demodulation         : 0.05
% 2.37/1.29  BG Simplification    : 0.01
% 2.37/1.29  Subsumption          : 0.03
% 2.37/1.29  Abstraction          : 0.01
% 2.37/1.29  MUC search           : 0.00
% 2.37/1.29  Cooper               : 0.00
% 2.37/1.29  Total                : 0.54
% 2.37/1.29  Index Insertion      : 0.00
% 2.37/1.29  Index Deletion       : 0.00
% 2.37/1.29  Index Matching       : 0.00
% 2.37/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
