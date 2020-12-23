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
% DateTime   : Thu Dec  3 10:15:46 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 212 expanded)
%              Number of leaves         :   40 (  97 expanded)
%              Depth                    :    9
%              Number of atoms          :  135 ( 714 expanded)
%              Number of equality atoms :   39 ( 193 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
         => ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_58,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_62,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_60,plain,(
    v1_funct_2('#skF_7','#skF_6','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_56,plain,(
    v2_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_50,plain,(
    k1_funct_1('#skF_7','#skF_9') = k1_funct_1('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_52,plain,(
    r2_hidden('#skF_9','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_942,plain,(
    ! [D_225,C_226,B_227,A_228] :
      ( k1_funct_1(k2_funct_1(D_225),k1_funct_1(D_225,C_226)) = C_226
      | k1_xboole_0 = B_227
      | ~ r2_hidden(C_226,A_228)
      | ~ v2_funct_1(D_225)
      | ~ m1_subset_1(D_225,k1_zfmisc_1(k2_zfmisc_1(A_228,B_227)))
      | ~ v1_funct_2(D_225,A_228,B_227)
      | ~ v1_funct_1(D_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1029,plain,(
    ! [D_233,B_234] :
      ( k1_funct_1(k2_funct_1(D_233),k1_funct_1(D_233,'#skF_9')) = '#skF_9'
      | k1_xboole_0 = B_234
      | ~ v2_funct_1(D_233)
      | ~ m1_subset_1(D_233,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_234)))
      | ~ v1_funct_2(D_233,'#skF_6',B_234)
      | ~ v1_funct_1(D_233) ) ),
    inference(resolution,[status(thm)],[c_52,c_942])).

tff(c_1031,plain,
    ( k1_funct_1(k2_funct_1('#skF_7'),k1_funct_1('#skF_7','#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_6'
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_2('#skF_7','#skF_6','#skF_6')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_1029])).

tff(c_1037,plain,
    ( k1_funct_1(k2_funct_1('#skF_7'),k1_funct_1('#skF_7','#skF_8')) = '#skF_9'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_50,c_1031])).

tff(c_1049,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1037])).

tff(c_10,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1060,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_6',B_6) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_1049,c_10])).

tff(c_1066,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1060,c_58])).

tff(c_152,plain,(
    ! [C_90,B_91,A_92] :
      ( v5_relat_1(C_90,B_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_92,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_158,plain,(
    ! [C_90,B_6] :
      ( v5_relat_1(C_90,B_6)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_152])).

tff(c_1134,plain,(
    ! [C_243,B_244] :
      ( v5_relat_1(C_243,B_244)
      | ~ m1_subset_1(C_243,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_158])).

tff(c_1137,plain,(
    ! [B_244] : v5_relat_1('#skF_7',B_244) ),
    inference(resolution,[status(thm)],[c_1066,c_1134])).

tff(c_116,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_124,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_116])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k2_relat_1(B_8),A_7)
      | ~ v5_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_175,plain,(
    ! [A_98,B_99,C_100] :
      ( k1_relset_1(A_98,B_99,C_100) = k1_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_185,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_175])).

tff(c_279,plain,(
    ! [A_125,B_126] :
      ( k1_relset_1(A_125,A_125,B_126) = A_125
      | ~ m1_subset_1(B_126,k1_zfmisc_1(k2_zfmisc_1(A_125,A_125)))
      | ~ v1_funct_2(B_126,A_125,A_125)
      | ~ v1_funct_1(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_282,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_7') = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_6','#skF_6')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_279])).

tff(c_293,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_185,c_282])).

tff(c_186,plain,(
    ! [A_101,D_102] :
      ( r2_hidden(k1_funct_1(A_101,D_102),k2_relat_1(A_101))
      | ~ r2_hidden(D_102,k1_relat_1(A_101))
      | ~ v1_funct_1(A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_195,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_8'),k2_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_186])).

tff(c_199,plain,
    ( r2_hidden(k1_funct_1('#skF_7','#skF_8'),k2_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_62,c_195])).

tff(c_204,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_199])).

tff(c_294,plain,(
    ~ r2_hidden('#skF_9','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_204])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_294])).

tff(c_299,plain,(
    r2_hidden(k1_funct_1('#skF_7','#skF_8'),k2_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_34,plain,(
    ! [B_50,A_49] :
      ( ~ r1_tarski(B_50,A_49)
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_327,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),k1_funct_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_299,c_34])).

tff(c_331,plain,
    ( ~ v5_relat_1('#skF_7',k1_funct_1('#skF_7','#skF_8'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_14,c_327])).

tff(c_334,plain,(
    ~ v5_relat_1('#skF_7',k1_funct_1('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_331])).

tff(c_1143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1137,c_334])).

tff(c_1145,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1037])).

tff(c_48,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1144,plain,(
    k1_funct_1(k2_funct_1('#skF_7'),k1_funct_1('#skF_7','#skF_8')) = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1037])).

tff(c_54,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1039,plain,(
    ! [D_235,B_236] :
      ( k1_funct_1(k2_funct_1(D_235),k1_funct_1(D_235,'#skF_8')) = '#skF_8'
      | k1_xboole_0 = B_236
      | ~ v2_funct_1(D_235)
      | ~ m1_subset_1(D_235,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_236)))
      | ~ v1_funct_2(D_235,'#skF_6',B_236)
      | ~ v1_funct_1(D_235) ) ),
    inference(resolution,[status(thm)],[c_54,c_942])).

tff(c_1041,plain,
    ( k1_funct_1(k2_funct_1('#skF_7'),k1_funct_1('#skF_7','#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_6'
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_2('#skF_7','#skF_6','#skF_6')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_1039])).

tff(c_1047,plain,
    ( k1_funct_1(k2_funct_1('#skF_7'),k1_funct_1('#skF_7','#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_1041])).

tff(c_1163,plain,
    ( '#skF_9' = '#skF_8'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1144,c_1047])).

tff(c_1164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1145,c_48,c_1163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:47:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.54/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.59  
% 3.54/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/1.59  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 3.54/1.59  
% 3.54/1.59  %Foreground sorts:
% 3.54/1.59  
% 3.54/1.59  
% 3.54/1.59  %Background operators:
% 3.54/1.59  
% 3.54/1.59  
% 3.54/1.59  %Foreground operators:
% 3.54/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.54/1.59  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.54/1.59  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.54/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.54/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.54/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.54/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.54/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.54/1.59  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.54/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.54/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.54/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.54/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.54/1.59  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.54/1.59  tff('#skF_9', type, '#skF_9': $i).
% 3.54/1.59  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.54/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.54/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.54/1.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.54/1.59  tff('#skF_8', type, '#skF_8': $i).
% 3.54/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.54/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.54/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.54/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.54/1.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.54/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.54/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.54/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.54/1.59  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.54/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.54/1.59  
% 3.79/1.61  tff(f_117, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_funct_2)).
% 3.79/1.61  tff(f_91, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 3.79/1.61  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.79/1.61  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.79/1.61  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.79/1.61  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.79/1.61  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.79/1.61  tff(f_99, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 3.79/1.61  tff(f_58, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 3.79/1.61  tff(f_63, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.79/1.61  tff(c_62, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.79/1.61  tff(c_60, plain, (v1_funct_2('#skF_7', '#skF_6', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.79/1.61  tff(c_56, plain, (v2_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.79/1.61  tff(c_50, plain, (k1_funct_1('#skF_7', '#skF_9')=k1_funct_1('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.79/1.61  tff(c_58, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.79/1.61  tff(c_52, plain, (r2_hidden('#skF_9', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.79/1.61  tff(c_942, plain, (![D_225, C_226, B_227, A_228]: (k1_funct_1(k2_funct_1(D_225), k1_funct_1(D_225, C_226))=C_226 | k1_xboole_0=B_227 | ~r2_hidden(C_226, A_228) | ~v2_funct_1(D_225) | ~m1_subset_1(D_225, k1_zfmisc_1(k2_zfmisc_1(A_228, B_227))) | ~v1_funct_2(D_225, A_228, B_227) | ~v1_funct_1(D_225))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.79/1.61  tff(c_1029, plain, (![D_233, B_234]: (k1_funct_1(k2_funct_1(D_233), k1_funct_1(D_233, '#skF_9'))='#skF_9' | k1_xboole_0=B_234 | ~v2_funct_1(D_233) | ~m1_subset_1(D_233, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_234))) | ~v1_funct_2(D_233, '#skF_6', B_234) | ~v1_funct_1(D_233))), inference(resolution, [status(thm)], [c_52, c_942])).
% 3.79/1.61  tff(c_1031, plain, (k1_funct_1(k2_funct_1('#skF_7'), k1_funct_1('#skF_7', '#skF_9'))='#skF_9' | k1_xboole_0='#skF_6' | ~v2_funct_1('#skF_7') | ~v1_funct_2('#skF_7', '#skF_6', '#skF_6') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_1029])).
% 3.79/1.61  tff(c_1037, plain, (k1_funct_1(k2_funct_1('#skF_7'), k1_funct_1('#skF_7', '#skF_8'))='#skF_9' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_50, c_1031])).
% 3.79/1.61  tff(c_1049, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_1037])).
% 3.79/1.61  tff(c_10, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.79/1.61  tff(c_1060, plain, (![B_6]: (k2_zfmisc_1('#skF_6', B_6)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1049, c_1049, c_10])).
% 3.79/1.61  tff(c_1066, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1060, c_58])).
% 3.79/1.61  tff(c_152, plain, (![C_90, B_91, A_92]: (v5_relat_1(C_90, B_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_92, B_91))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.79/1.61  tff(c_158, plain, (![C_90, B_6]: (v5_relat_1(C_90, B_6) | ~m1_subset_1(C_90, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_152])).
% 3.79/1.61  tff(c_1134, plain, (![C_243, B_244]: (v5_relat_1(C_243, B_244) | ~m1_subset_1(C_243, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_1049, c_158])).
% 3.79/1.61  tff(c_1137, plain, (![B_244]: (v5_relat_1('#skF_7', B_244))), inference(resolution, [status(thm)], [c_1066, c_1134])).
% 3.79/1.61  tff(c_116, plain, (![C_75, A_76, B_77]: (v1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.79/1.61  tff(c_124, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_116])).
% 3.79/1.61  tff(c_14, plain, (![B_8, A_7]: (r1_tarski(k2_relat_1(B_8), A_7) | ~v5_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.79/1.61  tff(c_175, plain, (![A_98, B_99, C_100]: (k1_relset_1(A_98, B_99, C_100)=k1_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.79/1.61  tff(c_185, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_175])).
% 3.79/1.61  tff(c_279, plain, (![A_125, B_126]: (k1_relset_1(A_125, A_125, B_126)=A_125 | ~m1_subset_1(B_126, k1_zfmisc_1(k2_zfmisc_1(A_125, A_125))) | ~v1_funct_2(B_126, A_125, A_125) | ~v1_funct_1(B_126))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.79/1.61  tff(c_282, plain, (k1_relset_1('#skF_6', '#skF_6', '#skF_7')='#skF_6' | ~v1_funct_2('#skF_7', '#skF_6', '#skF_6') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_279])).
% 3.79/1.61  tff(c_293, plain, (k1_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_185, c_282])).
% 3.79/1.61  tff(c_186, plain, (![A_101, D_102]: (r2_hidden(k1_funct_1(A_101, D_102), k2_relat_1(A_101)) | ~r2_hidden(D_102, k1_relat_1(A_101)) | ~v1_funct_1(A_101) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.79/1.61  tff(c_195, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_8'), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_9', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_50, c_186])).
% 3.79/1.61  tff(c_199, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_8'), k2_relat_1('#skF_7')) | ~r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_62, c_195])).
% 3.79/1.61  tff(c_204, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_199])).
% 3.79/1.61  tff(c_294, plain, (~r2_hidden('#skF_9', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_293, c_204])).
% 3.79/1.61  tff(c_298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_294])).
% 3.79/1.61  tff(c_299, plain, (r2_hidden(k1_funct_1('#skF_7', '#skF_8'), k2_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_199])).
% 3.79/1.61  tff(c_34, plain, (![B_50, A_49]: (~r1_tarski(B_50, A_49) | ~r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.79/1.61  tff(c_327, plain, (~r1_tarski(k2_relat_1('#skF_7'), k1_funct_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_299, c_34])).
% 3.79/1.61  tff(c_331, plain, (~v5_relat_1('#skF_7', k1_funct_1('#skF_7', '#skF_8')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_14, c_327])).
% 3.79/1.61  tff(c_334, plain, (~v5_relat_1('#skF_7', k1_funct_1('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_331])).
% 3.79/1.61  tff(c_1143, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1137, c_334])).
% 3.79/1.61  tff(c_1145, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_1037])).
% 3.79/1.61  tff(c_48, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.79/1.61  tff(c_1144, plain, (k1_funct_1(k2_funct_1('#skF_7'), k1_funct_1('#skF_7', '#skF_8'))='#skF_9'), inference(splitRight, [status(thm)], [c_1037])).
% 3.79/1.61  tff(c_54, plain, (r2_hidden('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.79/1.61  tff(c_1039, plain, (![D_235, B_236]: (k1_funct_1(k2_funct_1(D_235), k1_funct_1(D_235, '#skF_8'))='#skF_8' | k1_xboole_0=B_236 | ~v2_funct_1(D_235) | ~m1_subset_1(D_235, k1_zfmisc_1(k2_zfmisc_1('#skF_6', B_236))) | ~v1_funct_2(D_235, '#skF_6', B_236) | ~v1_funct_1(D_235))), inference(resolution, [status(thm)], [c_54, c_942])).
% 3.79/1.61  tff(c_1041, plain, (k1_funct_1(k2_funct_1('#skF_7'), k1_funct_1('#skF_7', '#skF_8'))='#skF_8' | k1_xboole_0='#skF_6' | ~v2_funct_1('#skF_7') | ~v1_funct_2('#skF_7', '#skF_6', '#skF_6') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_1039])).
% 3.79/1.61  tff(c_1047, plain, (k1_funct_1(k2_funct_1('#skF_7'), k1_funct_1('#skF_7', '#skF_8'))='#skF_8' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_1041])).
% 3.79/1.61  tff(c_1163, plain, ('#skF_9'='#skF_8' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1144, c_1047])).
% 3.79/1.61  tff(c_1164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1145, c_48, c_1163])).
% 3.79/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.61  
% 3.79/1.61  Inference rules
% 3.79/1.61  ----------------------
% 3.79/1.61  #Ref     : 0
% 3.79/1.61  #Sup     : 249
% 3.79/1.61  #Fact    : 0
% 3.79/1.61  #Define  : 0
% 3.79/1.61  #Split   : 2
% 3.79/1.61  #Chain   : 0
% 3.79/1.61  #Close   : 0
% 3.79/1.61  
% 3.79/1.61  Ordering : KBO
% 3.79/1.61  
% 3.79/1.61  Simplification rules
% 3.79/1.61  ----------------------
% 3.79/1.61  #Subsume      : 60
% 3.79/1.61  #Demod        : 147
% 3.79/1.61  #Tautology    : 55
% 3.79/1.61  #SimpNegUnit  : 2
% 3.79/1.61  #BackRed      : 21
% 3.79/1.61  
% 3.79/1.61  #Partial instantiations: 0
% 3.79/1.61  #Strategies tried      : 1
% 3.79/1.61  
% 3.79/1.61  Timing (in seconds)
% 3.79/1.61  ----------------------
% 3.79/1.61  Preprocessing        : 0.31
% 3.79/1.61  Parsing              : 0.16
% 3.79/1.61  CNF conversion       : 0.03
% 3.79/1.61  Main loop            : 0.49
% 3.79/1.61  Inferencing          : 0.18
% 3.79/1.61  Reduction            : 0.14
% 3.79/1.61  Demodulation         : 0.09
% 3.79/1.61  BG Simplification    : 0.03
% 3.79/1.61  Subsumption          : 0.11
% 3.79/1.61  Abstraction          : 0.03
% 3.79/1.61  MUC search           : 0.00
% 3.79/1.61  Cooper               : 0.00
% 3.79/1.61  Total                : 0.84
% 3.79/1.61  Index Insertion      : 0.00
% 3.79/1.61  Index Deletion       : 0.00
% 3.79/1.61  Index Matching       : 0.00
% 3.79/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
