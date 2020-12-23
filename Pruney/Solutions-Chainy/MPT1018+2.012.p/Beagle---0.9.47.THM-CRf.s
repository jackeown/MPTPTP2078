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
% DateTime   : Thu Dec  3 10:15:47 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 309 expanded)
%              Number of leaves         :   33 ( 128 expanded)
%              Depth                    :   11
%              Number of atoms          :  195 (1143 expanded)
%              Number of equality atoms :   69 ( 307 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
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

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(c_34,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_57,plain,(
    ! [B_31,A_32] :
      ( v1_relat_1(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_32))
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_60,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_57])).

tff(c_63,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_60])).

tff(c_87,plain,(
    ! [C_36,A_37,B_38] :
      ( v4_relat_1(C_36,A_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_91,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_87])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_42,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_284,plain,(
    ! [D_74,C_75,B_76,A_77] :
      ( k1_funct_1(k2_funct_1(D_74),k1_funct_1(D_74,C_75)) = C_75
      | k1_xboole_0 = B_76
      | ~ r2_hidden(C_75,A_77)
      | ~ v2_funct_1(D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76)))
      | ~ v1_funct_2(D_74,A_77,B_76)
      | ~ v1_funct_1(D_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_300,plain,(
    ! [D_78,B_79] :
      ( k1_funct_1(k2_funct_1(D_78),k1_funct_1(D_78,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_79
      | ~ v2_funct_1(D_78)
      | ~ m1_subset_1(D_78,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_79)))
      | ~ v1_funct_2(D_78,'#skF_3',B_79)
      | ~ v1_funct_1(D_78) ) ),
    inference(resolution,[status(thm)],[c_38,c_284])).

tff(c_302,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_300])).

tff(c_305,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_302])).

tff(c_306,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_305])).

tff(c_92,plain,(
    ! [B_39,A_40] :
      ( r1_tarski(k1_relat_1(B_39),A_40)
      | ~ v4_relat_1(B_39,A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    ! [B_33,A_34] :
      ( B_33 = A_34
      | ~ r1_tarski(B_33,A_34)
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_64])).

tff(c_99,plain,(
    ! [B_39] :
      ( k1_relat_1(B_39) = k1_xboole_0
      | ~ v4_relat_1(B_39,k1_xboole_0)
      | ~ v1_relat_1(B_39) ) ),
    inference(resolution,[status(thm)],[c_92,c_73])).

tff(c_358,plain,(
    ! [B_86] :
      ( k1_relat_1(B_86) = '#skF_3'
      | ~ v4_relat_1(B_86,'#skF_3')
      | ~ v1_relat_1(B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_306,c_99])).

tff(c_361,plain,
    ( k1_relat_1('#skF_4') = '#skF_3'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_91,c_358])).

tff(c_364,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_361])).

tff(c_40,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_170,plain,(
    ! [D_59,C_60,B_61,A_62] :
      ( k1_funct_1(k2_funct_1(D_59),k1_funct_1(D_59,C_60)) = C_60
      | k1_xboole_0 = B_61
      | ~ r2_hidden(C_60,A_62)
      | ~ v2_funct_1(D_59)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_62,B_61)))
      | ~ v1_funct_2(D_59,A_62,B_61)
      | ~ v1_funct_1(D_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_183,plain,(
    ! [D_63,B_64] :
      ( k1_funct_1(k2_funct_1(D_63),k1_funct_1(D_63,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_64
      | ~ v2_funct_1(D_63)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_64)))
      | ~ v1_funct_2(D_63,'#skF_3',B_64)
      | ~ v1_funct_1(D_63) ) ),
    inference(resolution,[status(thm)],[c_38,c_170])).

tff(c_185,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_183])).

tff(c_188,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_185])).

tff(c_195,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_188])).

tff(c_234,plain,(
    ! [B_69] :
      ( k1_relat_1(B_69) = '#skF_3'
      | ~ v4_relat_1(B_69,'#skF_3')
      | ~ v1_relat_1(B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_195,c_99])).

tff(c_237,plain,
    ( k1_relat_1('#skF_4') = '#skF_3'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_91,c_234])).

tff(c_240,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_237])).

tff(c_36,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_156,plain,(
    ! [C_56,B_57,A_58] :
      ( C_56 = B_57
      | k1_funct_1(A_58,C_56) != k1_funct_1(A_58,B_57)
      | ~ r2_hidden(C_56,k1_relat_1(A_58))
      | ~ r2_hidden(B_57,k1_relat_1(A_58))
      | ~ v2_funct_1(A_58)
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_162,plain,(
    ! [B_57] :
      ( B_57 = '#skF_5'
      | k1_funct_1('#skF_4',B_57) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ r2_hidden(B_57,k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_156])).

tff(c_166,plain,(
    ! [B_57] :
      ( B_57 = '#skF_5'
      | k1_funct_1('#skF_4',B_57) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ r2_hidden(B_57,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48,c_42,c_162])).

tff(c_169,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_241,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_169])).

tff(c_244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_241])).

tff(c_246,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_245,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_188])).

tff(c_189,plain,(
    ! [D_65,B_66] :
      ( k1_funct_1(k2_funct_1(D_65),k1_funct_1(D_65,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_66
      | ~ v2_funct_1(D_65)
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_66)))
      | ~ v1_funct_2(D_65,'#skF_3',B_66)
      | ~ v1_funct_1(D_65) ) ),
    inference(resolution,[status(thm)],[c_40,c_170])).

tff(c_191,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_189])).

tff(c_194,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_36,c_191])).

tff(c_256,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_194])).

tff(c_257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_246,c_34,c_256])).

tff(c_259,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_164,plain,(
    ! [C_56] :
      ( C_56 = '#skF_5'
      | k1_funct_1('#skF_4',C_56) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(C_56,k1_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_156])).

tff(c_168,plain,(
    ! [C_56] :
      ( C_56 = '#skF_5'
      | k1_funct_1('#skF_4',C_56) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(C_56,k1_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48,c_42,c_164])).

tff(c_261,plain,(
    ! [C_56] :
      ( C_56 = '#skF_5'
      | k1_funct_1('#skF_4',C_56) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(C_56,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_168])).

tff(c_427,plain,(
    ! [C_91] :
      ( C_91 = '#skF_5'
      | k1_funct_1('#skF_4',C_91) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(C_91,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_261])).

tff(c_430,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_38,c_427])).

tff(c_437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_430])).

tff(c_439,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_305])).

tff(c_438,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_305])).

tff(c_448,plain,(
    ! [D_92,B_93] :
      ( k1_funct_1(k2_funct_1(D_92),k1_funct_1(D_92,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_93
      | ~ v2_funct_1(D_92)
      | ~ m1_subset_1(D_92,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_93)))
      | ~ v1_funct_2(D_92,'#skF_3',B_93)
      | ~ v1_funct_1(D_92) ) ),
    inference(resolution,[status(thm)],[c_40,c_284])).

tff(c_450,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_448])).

tff(c_453,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42,c_438,c_36,c_450])).

tff(c_455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_439,c_34,c_453])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.34  
% 2.56/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.35  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.56/1.35  
% 2.56/1.35  %Foreground sorts:
% 2.56/1.35  
% 2.56/1.35  
% 2.56/1.35  %Background operators:
% 2.56/1.35  
% 2.56/1.35  
% 2.56/1.35  %Foreground operators:
% 2.56/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.56/1.35  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.56/1.35  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.56/1.35  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.56/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.56/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.56/1.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.56/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.56/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.56/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.56/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.56/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.56/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.56/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.56/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.35  
% 2.56/1.37  tff(f_101, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) => (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_funct_2)).
% 2.56/1.37  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.56/1.37  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.56/1.37  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.56/1.37  tff(f_83, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 2.56/1.37  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.56/1.37  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.56/1.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.56/1.37  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 2.56/1.37  tff(c_34, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.56/1.37  tff(c_38, plain, (r2_hidden('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.56/1.37  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.56/1.37  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.56/1.37  tff(c_57, plain, (![B_31, A_32]: (v1_relat_1(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(A_32)) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.56/1.37  tff(c_60, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_57])).
% 2.56/1.37  tff(c_63, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_60])).
% 2.56/1.37  tff(c_87, plain, (![C_36, A_37, B_38]: (v4_relat_1(C_36, A_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.56/1.37  tff(c_91, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_87])).
% 2.56/1.37  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.56/1.37  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.56/1.37  tff(c_42, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.56/1.37  tff(c_284, plain, (![D_74, C_75, B_76, A_77]: (k1_funct_1(k2_funct_1(D_74), k1_funct_1(D_74, C_75))=C_75 | k1_xboole_0=B_76 | ~r2_hidden(C_75, A_77) | ~v2_funct_1(D_74) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))) | ~v1_funct_2(D_74, A_77, B_76) | ~v1_funct_1(D_74))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.37  tff(c_300, plain, (![D_78, B_79]: (k1_funct_1(k2_funct_1(D_78), k1_funct_1(D_78, '#skF_6'))='#skF_6' | k1_xboole_0=B_79 | ~v2_funct_1(D_78) | ~m1_subset_1(D_78, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_79))) | ~v1_funct_2(D_78, '#skF_3', B_79) | ~v1_funct_1(D_78))), inference(resolution, [status(thm)], [c_38, c_284])).
% 2.56/1.37  tff(c_302, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_300])).
% 2.56/1.37  tff(c_305, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_302])).
% 2.56/1.37  tff(c_306, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_305])).
% 2.56/1.37  tff(c_92, plain, (![B_39, A_40]: (r1_tarski(k1_relat_1(B_39), A_40) | ~v4_relat_1(B_39, A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.56/1.37  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.56/1.37  tff(c_64, plain, (![B_33, A_34]: (B_33=A_34 | ~r1_tarski(B_33, A_34) | ~r1_tarski(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.37  tff(c_73, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_64])).
% 2.56/1.37  tff(c_99, plain, (![B_39]: (k1_relat_1(B_39)=k1_xboole_0 | ~v4_relat_1(B_39, k1_xboole_0) | ~v1_relat_1(B_39))), inference(resolution, [status(thm)], [c_92, c_73])).
% 2.56/1.37  tff(c_358, plain, (![B_86]: (k1_relat_1(B_86)='#skF_3' | ~v4_relat_1(B_86, '#skF_3') | ~v1_relat_1(B_86))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_306, c_99])).
% 2.56/1.37  tff(c_361, plain, (k1_relat_1('#skF_4')='#skF_3' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_91, c_358])).
% 2.56/1.37  tff(c_364, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_361])).
% 2.56/1.37  tff(c_40, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.56/1.37  tff(c_170, plain, (![D_59, C_60, B_61, A_62]: (k1_funct_1(k2_funct_1(D_59), k1_funct_1(D_59, C_60))=C_60 | k1_xboole_0=B_61 | ~r2_hidden(C_60, A_62) | ~v2_funct_1(D_59) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_62, B_61))) | ~v1_funct_2(D_59, A_62, B_61) | ~v1_funct_1(D_59))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.56/1.37  tff(c_183, plain, (![D_63, B_64]: (k1_funct_1(k2_funct_1(D_63), k1_funct_1(D_63, '#skF_6'))='#skF_6' | k1_xboole_0=B_64 | ~v2_funct_1(D_63) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_64))) | ~v1_funct_2(D_63, '#skF_3', B_64) | ~v1_funct_1(D_63))), inference(resolution, [status(thm)], [c_38, c_170])).
% 2.56/1.37  tff(c_185, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_183])).
% 2.56/1.37  tff(c_188, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_185])).
% 2.56/1.37  tff(c_195, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_188])).
% 2.56/1.37  tff(c_234, plain, (![B_69]: (k1_relat_1(B_69)='#skF_3' | ~v4_relat_1(B_69, '#skF_3') | ~v1_relat_1(B_69))), inference(demodulation, [status(thm), theory('equality')], [c_195, c_195, c_99])).
% 2.56/1.37  tff(c_237, plain, (k1_relat_1('#skF_4')='#skF_3' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_91, c_234])).
% 2.56/1.37  tff(c_240, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_237])).
% 2.56/1.37  tff(c_36, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.56/1.37  tff(c_156, plain, (![C_56, B_57, A_58]: (C_56=B_57 | k1_funct_1(A_58, C_56)!=k1_funct_1(A_58, B_57) | ~r2_hidden(C_56, k1_relat_1(A_58)) | ~r2_hidden(B_57, k1_relat_1(A_58)) | ~v2_funct_1(A_58) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.56/1.37  tff(c_162, plain, (![B_57]: (B_57='#skF_5' | k1_funct_1('#skF_4', B_57)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~r2_hidden(B_57, k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_156])).
% 2.56/1.37  tff(c_166, plain, (![B_57]: (B_57='#skF_5' | k1_funct_1('#skF_4', B_57)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~r2_hidden(B_57, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_48, c_42, c_162])).
% 2.56/1.37  tff(c_169, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_166])).
% 2.56/1.37  tff(c_241, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_240, c_169])).
% 2.56/1.37  tff(c_244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_241])).
% 2.56/1.37  tff(c_246, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_188])).
% 2.56/1.37  tff(c_245, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_188])).
% 2.56/1.37  tff(c_189, plain, (![D_65, B_66]: (k1_funct_1(k2_funct_1(D_65), k1_funct_1(D_65, '#skF_5'))='#skF_5' | k1_xboole_0=B_66 | ~v2_funct_1(D_65) | ~m1_subset_1(D_65, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_66))) | ~v1_funct_2(D_65, '#skF_3', B_66) | ~v1_funct_1(D_65))), inference(resolution, [status(thm)], [c_40, c_170])).
% 2.56/1.37  tff(c_191, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_189])).
% 2.56/1.37  tff(c_194, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_36, c_191])).
% 2.56/1.37  tff(c_256, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_245, c_194])).
% 2.56/1.37  tff(c_257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_246, c_34, c_256])).
% 2.56/1.37  tff(c_259, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_166])).
% 2.56/1.37  tff(c_164, plain, (![C_56]: (C_56='#skF_5' | k1_funct_1('#skF_4', C_56)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(C_56, k1_relat_1('#skF_4')) | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_156])).
% 2.56/1.37  tff(c_168, plain, (![C_56]: (C_56='#skF_5' | k1_funct_1('#skF_4', C_56)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(C_56, k1_relat_1('#skF_4')) | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_48, c_42, c_164])).
% 2.56/1.37  tff(c_261, plain, (![C_56]: (C_56='#skF_5' | k1_funct_1('#skF_4', C_56)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(C_56, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_259, c_168])).
% 2.56/1.37  tff(c_427, plain, (![C_91]: (C_91='#skF_5' | k1_funct_1('#skF_4', C_91)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(C_91, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_364, c_261])).
% 2.56/1.37  tff(c_430, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_38, c_427])).
% 2.56/1.37  tff(c_437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_430])).
% 2.56/1.37  tff(c_439, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_305])).
% 2.56/1.37  tff(c_438, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_305])).
% 2.56/1.37  tff(c_448, plain, (![D_92, B_93]: (k1_funct_1(k2_funct_1(D_92), k1_funct_1(D_92, '#skF_5'))='#skF_5' | k1_xboole_0=B_93 | ~v2_funct_1(D_92) | ~m1_subset_1(D_92, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_93))) | ~v1_funct_2(D_92, '#skF_3', B_93) | ~v1_funct_1(D_92))), inference(resolution, [status(thm)], [c_40, c_284])).
% 2.56/1.37  tff(c_450, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_448])).
% 2.56/1.37  tff(c_453, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42, c_438, c_36, c_450])).
% 2.56/1.37  tff(c_455, plain, $false, inference(negUnitSimplification, [status(thm)], [c_439, c_34, c_453])).
% 2.56/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.37  
% 2.56/1.37  Inference rules
% 2.56/1.37  ----------------------
% 2.56/1.37  #Ref     : 1
% 2.56/1.37  #Sup     : 79
% 2.56/1.37  #Fact    : 0
% 2.56/1.37  #Define  : 0
% 2.56/1.37  #Split   : 3
% 2.56/1.37  #Chain   : 0
% 2.56/1.37  #Close   : 0
% 2.56/1.37  
% 2.56/1.37  Ordering : KBO
% 2.56/1.37  
% 2.56/1.37  Simplification rules
% 2.56/1.37  ----------------------
% 2.56/1.37  #Subsume      : 10
% 2.56/1.37  #Demod        : 91
% 2.56/1.37  #Tautology    : 42
% 2.56/1.37  #SimpNegUnit  : 3
% 2.56/1.37  #BackRed      : 14
% 2.56/1.37  
% 2.56/1.37  #Partial instantiations: 0
% 2.56/1.37  #Strategies tried      : 1
% 2.56/1.37  
% 2.56/1.37  Timing (in seconds)
% 2.56/1.37  ----------------------
% 2.56/1.37  Preprocessing        : 0.32
% 2.56/1.37  Parsing              : 0.17
% 2.56/1.37  CNF conversion       : 0.02
% 2.56/1.37  Main loop            : 0.28
% 2.56/1.37  Inferencing          : 0.11
% 2.56/1.37  Reduction            : 0.09
% 2.56/1.37  Demodulation         : 0.06
% 2.56/1.37  BG Simplification    : 0.02
% 2.56/1.37  Subsumption          : 0.05
% 2.56/1.37  Abstraction          : 0.01
% 2.56/1.37  MUC search           : 0.00
% 2.56/1.37  Cooper               : 0.00
% 2.56/1.37  Total                : 0.65
% 2.56/1.37  Index Insertion      : 0.00
% 2.56/1.37  Index Deletion       : 0.00
% 2.56/1.37  Index Matching       : 0.00
% 2.56/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
