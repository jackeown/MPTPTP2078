%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:49 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 372 expanded)
%              Number of leaves         :   27 ( 125 expanded)
%              Depth                    :   15
%              Number of atoms          :  136 ( 960 expanded)
%              Number of equality atoms :   31 ( 298 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_37,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_69,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(c_4,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( v1_xboole_0(k2_zfmisc_1(A_4,B_5))
      | ~ v1_xboole_0(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_103,plain,(
    ! [C_27,B_28,A_29] :
      ( ~ v1_xboole_0(C_27)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(C_27))
      | ~ r2_hidden(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_112,plain,(
    ! [A_29] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_29,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_103])).

tff(c_113,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_117,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_113])).

tff(c_22,plain,(
    ~ v1_partfun1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_28,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_123,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_partfun1(C_30,A_31)
      | ~ v1_funct_2(C_30,A_31,B_32)
      | ~ v1_funct_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | v1_xboole_0(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_135,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_123])).

tff(c_142,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_135])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_117,c_22,c_142])).

tff(c_147,plain,(
    ! [A_33] : ~ r2_hidden(A_33,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_152,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4,c_147])).

tff(c_24,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_160,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_42])).

tff(c_188,plain,(
    ! [C_34,A_35,B_36] :
      ( v1_partfun1(C_34,A_35)
      | ~ v1_funct_2(C_34,A_35,B_36)
      | ~ v1_funct_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | v1_xboole_0(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_194,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_188])).

tff(c_199,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_194])).

tff(c_200,plain,(
    v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_199])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_202,plain,(
    ! [A_37] :
      ( A_37 = '#skF_4'
      | ~ v1_xboole_0(A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_2])).

tff(c_205,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_200,c_202])).

tff(c_215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_205])).

tff(c_217,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_265,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | A_2 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_4])).

tff(c_216,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_223,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_216])).

tff(c_229,plain,(
    ~ v1_partfun1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_22])).

tff(c_228,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_28])).

tff(c_262,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_32])).

tff(c_267,plain,(
    ! [A_41,B_42] :
      ( v1_xboole_0(k2_zfmisc_1(A_41,B_42))
      | ~ v1_xboole_0(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_263,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_2])).

tff(c_272,plain,(
    ! [A_43,B_44] :
      ( k2_zfmisc_1(A_43,B_44) = '#skF_3'
      | ~ v1_xboole_0(B_44) ) ),
    inference(resolution,[status(thm)],[c_267,c_263])).

tff(c_280,plain,(
    ! [A_46,A_47,B_48] :
      ( k2_zfmisc_1(A_46,k2_zfmisc_1(A_47,B_48)) = '#skF_3'
      | ~ v1_xboole_0(B_48) ) ),
    inference(resolution,[status(thm)],[c_6,c_272])).

tff(c_293,plain,(
    ! [A_47,B_48] :
      ( v1_xboole_0('#skF_3')
      | ~ v1_xboole_0(k2_zfmisc_1(A_47,B_48))
      | ~ v1_xboole_0(B_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_6])).

tff(c_313,plain,(
    ! [A_52,B_53] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_52,B_53))
      | ~ v1_xboole_0(B_53) ) ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_320,plain,(
    ! [B_5] : ~ v1_xboole_0(B_5) ),
    inference(resolution,[status(thm)],[c_6,c_313])).

tff(c_12,plain,(
    ! [C_12,A_9,B_10] :
      ( v1_partfun1(C_12,A_9)
      | ~ v1_funct_2(C_12,A_9,B_10)
      | ~ v1_funct_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | v1_xboole_0(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_324,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_partfun1(C_55,A_56)
      | ~ v1_funct_2(C_55,A_56,B_57)
      | ~ v1_funct_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_12])).

tff(c_333,plain,
    ( v1_partfun1('#skF_4','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_262,c_324])).

tff(c_340,plain,(
    v1_partfun1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_228,c_333])).

tff(c_342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_340])).

tff(c_343,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_271,plain,(
    ! [A_41,B_42] :
      ( k2_zfmisc_1(A_41,B_42) = '#skF_3'
      | ~ v1_xboole_0(B_42) ) ),
    inference(resolution,[status(thm)],[c_267,c_263])).

tff(c_349,plain,(
    ! [A_41] : k2_zfmisc_1(A_41,'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_343,c_271])).

tff(c_353,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_262])).

tff(c_377,plain,(
    ! [C_59,B_60,A_61] :
      ( ~ v1_xboole_0(C_59)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(C_59))
      | ~ r2_hidden(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_379,plain,(
    ! [A_61] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_61,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_353,c_377])).

tff(c_391,plain,(
    ! [A_62] : ~ r2_hidden(A_62,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_379])).

tff(c_396,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_265,c_391])).

tff(c_408,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_229])).

tff(c_239,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_218,plain,(
    k6_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_216,c_10])).

tff(c_234,plain,(
    k6_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_223,c_218])).

tff(c_245,plain,(
    k6_partfun1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_234])).

tff(c_406,plain,(
    k6_partfun1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_396,c_245])).

tff(c_16,plain,(
    ! [A_13] : v1_partfun1(k6_partfun1(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_437,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_16])).

tff(c_441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_408,c_437])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:09:06 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.31  
% 2.07/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.32  %$ v1_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.07/1.32  
% 2.07/1.32  %Foreground sorts:
% 2.07/1.32  
% 2.07/1.32  
% 2.07/1.32  %Background operators:
% 2.07/1.32  
% 2.07/1.32  
% 2.07/1.32  %Foreground operators:
% 2.07/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.07/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.07/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.07/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.32  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.07/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.32  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.07/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.07/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.07/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.07/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.32  
% 2.46/1.33  tff(f_37, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.46/1.33  tff(f_41, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 2.46/1.33  tff(f_87, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 2.46/1.33  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.46/1.33  tff(f_63, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.46/1.33  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.46/1.33  tff(f_69, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.46/1.33  tff(f_49, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.46/1.33  tff(f_67, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.46/1.33  tff(c_4, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.46/1.33  tff(c_6, plain, (![A_4, B_5]: (v1_xboole_0(k2_zfmisc_1(A_4, B_5)) | ~v1_xboole_0(B_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.46/1.33  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.46/1.33  tff(c_103, plain, (![C_27, B_28, A_29]: (~v1_xboole_0(C_27) | ~m1_subset_1(B_28, k1_zfmisc_1(C_27)) | ~r2_hidden(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.46/1.33  tff(c_112, plain, (![A_29]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_29, '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_103])).
% 2.46/1.33  tff(c_113, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_112])).
% 2.46/1.33  tff(c_117, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_6, c_113])).
% 2.46/1.33  tff(c_22, plain, (~v1_partfun1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.46/1.33  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.46/1.33  tff(c_28, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.46/1.33  tff(c_123, plain, (![C_30, A_31, B_32]: (v1_partfun1(C_30, A_31) | ~v1_funct_2(C_30, A_31, B_32) | ~v1_funct_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | v1_xboole_0(B_32))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.46/1.33  tff(c_135, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_123])).
% 2.46/1.33  tff(c_142, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_135])).
% 2.46/1.33  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_117, c_22, c_142])).
% 2.46/1.33  tff(c_147, plain, (![A_33]: (~r2_hidden(A_33, '#skF_4'))), inference(splitRight, [status(thm)], [c_112])).
% 2.46/1.33  tff(c_152, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4, c_147])).
% 2.46/1.33  tff(c_24, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.46/1.33  tff(c_42, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_24])).
% 2.46/1.33  tff(c_160, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_42])).
% 2.46/1.33  tff(c_188, plain, (![C_34, A_35, B_36]: (v1_partfun1(C_34, A_35) | ~v1_funct_2(C_34, A_35, B_36) | ~v1_funct_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | v1_xboole_0(B_36))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.46/1.33  tff(c_194, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_32, c_188])).
% 2.46/1.33  tff(c_199, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_194])).
% 2.46/1.33  tff(c_200, plain, (v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_22, c_199])).
% 2.46/1.33  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.46/1.33  tff(c_202, plain, (![A_37]: (A_37='#skF_4' | ~v1_xboole_0(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_2])).
% 2.46/1.33  tff(c_205, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_200, c_202])).
% 2.46/1.33  tff(c_215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_205])).
% 2.46/1.33  tff(c_217, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 2.46/1.33  tff(c_265, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | A_2='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_217, c_4])).
% 2.46/1.33  tff(c_216, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.46/1.33  tff(c_223, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_217, c_216])).
% 2.46/1.33  tff(c_229, plain, (~v1_partfun1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_22])).
% 2.46/1.33  tff(c_228, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_28])).
% 2.46/1.33  tff(c_262, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_32])).
% 2.46/1.33  tff(c_267, plain, (![A_41, B_42]: (v1_xboole_0(k2_zfmisc_1(A_41, B_42)) | ~v1_xboole_0(B_42))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.46/1.33  tff(c_263, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_2])).
% 2.46/1.33  tff(c_272, plain, (![A_43, B_44]: (k2_zfmisc_1(A_43, B_44)='#skF_3' | ~v1_xboole_0(B_44))), inference(resolution, [status(thm)], [c_267, c_263])).
% 2.46/1.33  tff(c_280, plain, (![A_46, A_47, B_48]: (k2_zfmisc_1(A_46, k2_zfmisc_1(A_47, B_48))='#skF_3' | ~v1_xboole_0(B_48))), inference(resolution, [status(thm)], [c_6, c_272])).
% 2.46/1.33  tff(c_293, plain, (![A_47, B_48]: (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1(A_47, B_48)) | ~v1_xboole_0(B_48))), inference(superposition, [status(thm), theory('equality')], [c_280, c_6])).
% 2.46/1.33  tff(c_313, plain, (![A_52, B_53]: (~v1_xboole_0(k2_zfmisc_1(A_52, B_53)) | ~v1_xboole_0(B_53))), inference(splitLeft, [status(thm)], [c_293])).
% 2.46/1.33  tff(c_320, plain, (![B_5]: (~v1_xboole_0(B_5))), inference(resolution, [status(thm)], [c_6, c_313])).
% 2.46/1.33  tff(c_12, plain, (![C_12, A_9, B_10]: (v1_partfun1(C_12, A_9) | ~v1_funct_2(C_12, A_9, B_10) | ~v1_funct_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))) | v1_xboole_0(B_10))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.46/1.33  tff(c_324, plain, (![C_55, A_56, B_57]: (v1_partfun1(C_55, A_56) | ~v1_funct_2(C_55, A_56, B_57) | ~v1_funct_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(negUnitSimplification, [status(thm)], [c_320, c_12])).
% 2.46/1.33  tff(c_333, plain, (v1_partfun1('#skF_4', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_262, c_324])).
% 2.46/1.33  tff(c_340, plain, (v1_partfun1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_228, c_333])).
% 2.46/1.33  tff(c_342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_229, c_340])).
% 2.46/1.33  tff(c_343, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_293])).
% 2.46/1.33  tff(c_271, plain, (![A_41, B_42]: (k2_zfmisc_1(A_41, B_42)='#skF_3' | ~v1_xboole_0(B_42))), inference(resolution, [status(thm)], [c_267, c_263])).
% 2.46/1.33  tff(c_349, plain, (![A_41]: (k2_zfmisc_1(A_41, '#skF_3')='#skF_3')), inference(resolution, [status(thm)], [c_343, c_271])).
% 2.46/1.33  tff(c_353, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_349, c_262])).
% 2.46/1.33  tff(c_377, plain, (![C_59, B_60, A_61]: (~v1_xboole_0(C_59) | ~m1_subset_1(B_60, k1_zfmisc_1(C_59)) | ~r2_hidden(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.46/1.33  tff(c_379, plain, (![A_61]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_61, '#skF_4'))), inference(resolution, [status(thm)], [c_353, c_377])).
% 2.46/1.33  tff(c_391, plain, (![A_62]: (~r2_hidden(A_62, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_343, c_379])).
% 2.46/1.33  tff(c_396, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_265, c_391])).
% 2.46/1.33  tff(c_408, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_396, c_229])).
% 2.46/1.33  tff(c_239, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.46/1.33  tff(c_10, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.46/1.33  tff(c_218, plain, (k6_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_216, c_216, c_10])).
% 2.46/1.33  tff(c_234, plain, (k6_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_223, c_223, c_218])).
% 2.46/1.33  tff(c_245, plain, (k6_partfun1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_239, c_234])).
% 2.46/1.33  tff(c_406, plain, (k6_partfun1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_396, c_396, c_245])).
% 2.46/1.33  tff(c_16, plain, (![A_13]: (v1_partfun1(k6_partfun1(A_13), A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.46/1.33  tff(c_437, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_406, c_16])).
% 2.46/1.33  tff(c_441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_408, c_437])).
% 2.46/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/1.33  
% 2.46/1.33  Inference rules
% 2.46/1.33  ----------------------
% 2.46/1.33  #Ref     : 0
% 2.46/1.33  #Sup     : 97
% 2.46/1.33  #Fact    : 0
% 2.46/1.33  #Define  : 0
% 2.46/1.33  #Split   : 4
% 2.46/1.33  #Chain   : 0
% 2.46/1.33  #Close   : 0
% 2.46/1.33  
% 2.46/1.33  Ordering : KBO
% 2.46/1.33  
% 2.46/1.33  Simplification rules
% 2.46/1.33  ----------------------
% 2.46/1.33  #Subsume      : 12
% 2.46/1.33  #Demod        : 75
% 2.46/1.33  #Tautology    : 55
% 2.46/1.33  #SimpNegUnit  : 7
% 2.46/1.33  #BackRed      : 30
% 2.46/1.33  
% 2.46/1.33  #Partial instantiations: 0
% 2.46/1.33  #Strategies tried      : 1
% 2.46/1.33  
% 2.46/1.33  Timing (in seconds)
% 2.46/1.33  ----------------------
% 2.46/1.34  Preprocessing        : 0.31
% 2.46/1.34  Parsing              : 0.16
% 2.46/1.34  CNF conversion       : 0.02
% 2.46/1.34  Main loop            : 0.25
% 2.46/1.34  Inferencing          : 0.09
% 2.46/1.34  Reduction            : 0.08
% 2.46/1.34  Demodulation         : 0.06
% 2.46/1.34  BG Simplification    : 0.01
% 2.46/1.34  Subsumption          : 0.03
% 2.46/1.34  Abstraction          : 0.01
% 2.46/1.34  MUC search           : 0.00
% 2.46/1.34  Cooper               : 0.00
% 2.46/1.34  Total                : 0.60
% 2.46/1.34  Index Insertion      : 0.00
% 2.46/1.34  Index Deletion       : 0.00
% 2.46/1.34  Index Matching       : 0.00
% 2.46/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
