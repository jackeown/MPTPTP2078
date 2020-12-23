%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:44 EST 2020

% Result     : Theorem 4.31s
% Output     : CNFRefutation 4.71s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 420 expanded)
%              Number of leaves         :   33 ( 153 expanded)
%              Depth                    :   11
%              Number of atoms          :  275 (1415 expanded)
%              Number of equality atoms :   73 ( 348 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_64,axiom,(
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

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(c_38,plain,
    ( '#skF_5' != '#skF_6'
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_57,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_10,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_60,plain,(
    ! [B_42,A_43] :
      ( v1_relat_1(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_63,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_60])).

tff(c_69,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_63])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_77,plain,(
    ! [A_44] :
      ( '#skF_2'(A_44) != '#skF_1'(A_44)
      | v2_funct_1(A_44)
      | ~ v1_funct_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_80,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_77,c_57])).

tff(c_83,plain,(
    '#skF_2'('#skF_4') != '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_36,c_80])).

tff(c_257,plain,(
    ! [A_74] :
      ( k1_funct_1(A_74,'#skF_2'(A_74)) = k1_funct_1(A_74,'#skF_1'(A_74))
      | v2_funct_1(A_74)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_56,plain,(
    ! [D_38,C_37] :
      ( v2_funct_1('#skF_4')
      | D_38 = C_37
      | k1_funct_1('#skF_4',D_38) != k1_funct_1('#skF_4',C_37)
      | ~ r2_hidden(D_38,'#skF_3')
      | ~ r2_hidden(C_37,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_147,plain,(
    ! [D_38,C_37] :
      ( D_38 = C_37
      | k1_funct_1('#skF_4',D_38) != k1_funct_1('#skF_4',C_37)
      | ~ r2_hidden(D_38,'#skF_3')
      | ~ r2_hidden(C_37,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_56])).

tff(c_266,plain,(
    ! [D_38] :
      ( D_38 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_38) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_38,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_147])).

tff(c_275,plain,(
    ! [D_38] :
      ( D_38 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_38) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_38,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_36,c_266])).

tff(c_276,plain,(
    ! [D_38] :
      ( D_38 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_38) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_38,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_275])).

tff(c_494,plain,(
    ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_276])).

tff(c_103,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_relset_1(A_56,B_57,C_58) = k1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_111,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_103])).

tff(c_124,plain,(
    ! [A_61,B_62,C_63] :
      ( m1_subset_1(k1_relset_1(A_61,B_62,C_63),k1_zfmisc_1(A_61))
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_139,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_124])).

tff(c_146,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_139])).

tff(c_95,plain,(
    ! [A_54] :
      ( r2_hidden('#skF_2'(A_54),k1_relat_1(A_54))
      | v2_funct_1(A_54)
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_560,plain,(
    ! [A_110,A_111] :
      ( r2_hidden('#skF_2'(A_110),A_111)
      | ~ m1_subset_1(k1_relat_1(A_110),k1_zfmisc_1(A_111))
      | v2_funct_1(A_110)
      | ~ v1_funct_1(A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(resolution,[status(thm)],[c_95,c_2])).

tff(c_578,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_146,c_560])).

tff(c_596,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_36,c_578])).

tff(c_598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_494,c_596])).

tff(c_600,plain,(
    r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_276])).

tff(c_263,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_37,'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_147])).

tff(c_272,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_37,'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_36,c_263])).

tff(c_273,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_37,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_272])).

tff(c_651,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(C_37,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_273])).

tff(c_654,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_651])).

tff(c_655,plain,(
    ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_654])).

tff(c_99,plain,(
    ! [A_55] :
      ( r2_hidden('#skF_1'(A_55),k1_relat_1(A_55))
      | v2_funct_1(A_55)
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_749,plain,(
    ! [A_124,A_125] :
      ( r2_hidden('#skF_1'(A_124),A_125)
      | ~ m1_subset_1(k1_relat_1(A_124),k1_zfmisc_1(A_125))
      | v2_funct_1(A_124)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_764,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_146,c_749])).

tff(c_779,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_36,c_764])).

tff(c_781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_655,c_779])).

tff(c_782,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_34,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_783,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_42,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_787,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_42])).

tff(c_1757,plain,(
    ! [D_236,C_237,B_238,A_239] :
      ( k1_funct_1(k2_funct_1(D_236),k1_funct_1(D_236,C_237)) = C_237
      | k1_xboole_0 = B_238
      | ~ r2_hidden(C_237,A_239)
      | ~ v2_funct_1(D_236)
      | ~ m1_subset_1(D_236,k1_zfmisc_1(k2_zfmisc_1(A_239,B_238)))
      | ~ v1_funct_2(D_236,A_239,B_238)
      | ~ v1_funct_1(D_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1848,plain,(
    ! [D_245,B_246] :
      ( k1_funct_1(k2_funct_1(D_245),k1_funct_1(D_245,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_246
      | ~ v2_funct_1(D_245)
      | ~ m1_subset_1(D_245,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_246)))
      | ~ v1_funct_2(D_245,'#skF_3',B_246)
      | ~ v1_funct_1(D_245) ) ),
    inference(resolution,[status(thm)],[c_787,c_1757])).

tff(c_1868,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_1848])).

tff(c_1880,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_783,c_1868])).

tff(c_1882,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1880])).

tff(c_4,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1909,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1882,c_4])).

tff(c_44,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_789,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_44])).

tff(c_814,plain,(
    ! [C_132,A_133,B_134] :
      ( r2_hidden(C_132,A_133)
      | ~ r2_hidden(C_132,B_134)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(A_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_819,plain,(
    ! [A_133] :
      ( r2_hidden('#skF_5',A_133)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_133)) ) ),
    inference(resolution,[status(thm)],[c_789,c_814])).

tff(c_1923,plain,(
    ! [A_133] : r2_hidden('#skF_5',A_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1909,c_819])).

tff(c_796,plain,(
    ! [B_129,A_130] :
      ( v1_relat_1(B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_130))
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_799,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_796])).

tff(c_805,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_799])).

tff(c_40,plain,
    ( k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_791,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_40])).

tff(c_1612,plain,(
    ! [B_221,A_222] :
      ( k1_funct_1(k2_funct_1(B_221),k1_funct_1(B_221,A_222)) = A_222
      | ~ r2_hidden(A_222,k1_relat_1(B_221))
      | ~ v2_funct_1(B_221)
      | ~ v1_funct_1(B_221)
      | ~ v1_relat_1(B_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1633,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5'
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_791,c_1612])).

tff(c_1637,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5'
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_805,c_36,c_783,c_1633])).

tff(c_1638,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1637])).

tff(c_1961,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1923,c_1638])).

tff(c_1963,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1880])).

tff(c_1962,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1880])).

tff(c_1964,plain,(
    ! [D_253,B_254] :
      ( k1_funct_1(k2_funct_1(D_253),k1_funct_1(D_253,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_254
      | ~ v2_funct_1(D_253)
      | ~ m1_subset_1(D_253,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_254)))
      | ~ v1_funct_2(D_253,'#skF_3',B_254)
      | ~ v1_funct_1(D_253) ) ),
    inference(resolution,[status(thm)],[c_789,c_1757])).

tff(c_1984,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_1964])).

tff(c_1996,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_783,c_791,c_1984])).

tff(c_2021,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1962,c_1996])).

tff(c_2022,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1963,c_782,c_2021])).

tff(c_2023,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1637])).

tff(c_2202,plain,(
    ! [D_270,C_271,B_272,A_273] :
      ( k1_funct_1(k2_funct_1(D_270),k1_funct_1(D_270,C_271)) = C_271
      | k1_xboole_0 = B_272
      | ~ r2_hidden(C_271,A_273)
      | ~ v2_funct_1(D_270)
      | ~ m1_subset_1(D_270,k1_zfmisc_1(k2_zfmisc_1(A_273,B_272)))
      | ~ v1_funct_2(D_270,A_273,B_272)
      | ~ v1_funct_1(D_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2245,plain,(
    ! [D_276,B_277] :
      ( k1_funct_1(k2_funct_1(D_276),k1_funct_1(D_276,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_277
      | ~ v2_funct_1(D_276)
      | ~ m1_subset_1(D_276,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_277)))
      | ~ v1_funct_2(D_276,'#skF_3',B_277)
      | ~ v1_funct_1(D_276) ) ),
    inference(resolution,[status(thm)],[c_787,c_2202])).

tff(c_2262,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_2245])).

tff(c_2273,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_783,c_2023,c_2262])).

tff(c_2274,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_782,c_2273])).

tff(c_2300,plain,(
    ! [A_5] : m1_subset_1('#skF_3',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2274,c_4])).

tff(c_820,plain,(
    ! [A_133] :
      ( r2_hidden('#skF_6',A_133)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_133)) ) ),
    inference(resolution,[status(thm)],[c_787,c_814])).

tff(c_2307,plain,(
    ! [A_133] : r2_hidden('#skF_6',A_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2300,c_820])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( k1_funct_1(k2_funct_1(B_22),k1_funct_1(B_22,A_21)) = A_21
      | ~ r2_hidden(A_21,k1_relat_1(B_22))
      | ~ v2_funct_1(B_22)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2039,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2023,c_24])).

tff(c_2046,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_805,c_36,c_783,c_2039])).

tff(c_2047,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_782,c_2046])).

tff(c_2339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2307,c_2047])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:09:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.31/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.31/1.77  
% 4.31/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.31/1.78  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 4.31/1.78  
% 4.31/1.78  %Foreground sorts:
% 4.31/1.78  
% 4.31/1.78  
% 4.31/1.78  %Background operators:
% 4.31/1.78  
% 4.31/1.78  
% 4.31/1.78  %Foreground operators:
% 4.31/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.31/1.78  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.31/1.78  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.31/1.78  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.31/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.31/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.31/1.78  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.31/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.31/1.78  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.31/1.78  tff('#skF_5', type, '#skF_5': $i).
% 4.31/1.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.31/1.78  tff('#skF_6', type, '#skF_6': $i).
% 4.31/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.31/1.78  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.31/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.31/1.78  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.31/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.31/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.31/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.31/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.31/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.31/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.31/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.31/1.78  
% 4.71/1.80  tff(f_116, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_funct_2)).
% 4.71/1.80  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.71/1.80  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.71/1.80  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 4.71/1.80  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.71/1.80  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 4.71/1.80  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 4.71/1.80  tff(f_98, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 4.71/1.80  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.71/1.80  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 4.71/1.80  tff(c_38, plain, ('#skF_5'!='#skF_6' | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.71/1.80  tff(c_57, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_38])).
% 4.71/1.80  tff(c_10, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.71/1.80  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.71/1.80  tff(c_60, plain, (![B_42, A_43]: (v1_relat_1(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.71/1.80  tff(c_63, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_60])).
% 4.71/1.80  tff(c_69, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_63])).
% 4.71/1.80  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.71/1.80  tff(c_77, plain, (![A_44]: ('#skF_2'(A_44)!='#skF_1'(A_44) | v2_funct_1(A_44) | ~v1_funct_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.71/1.80  tff(c_80, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_77, c_57])).
% 4.71/1.80  tff(c_83, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_36, c_80])).
% 4.71/1.80  tff(c_257, plain, (![A_74]: (k1_funct_1(A_74, '#skF_2'(A_74))=k1_funct_1(A_74, '#skF_1'(A_74)) | v2_funct_1(A_74) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.71/1.80  tff(c_56, plain, (![D_38, C_37]: (v2_funct_1('#skF_4') | D_38=C_37 | k1_funct_1('#skF_4', D_38)!=k1_funct_1('#skF_4', C_37) | ~r2_hidden(D_38, '#skF_3') | ~r2_hidden(C_37, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.71/1.80  tff(c_147, plain, (![D_38, C_37]: (D_38=C_37 | k1_funct_1('#skF_4', D_38)!=k1_funct_1('#skF_4', C_37) | ~r2_hidden(D_38, '#skF_3') | ~r2_hidden(C_37, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_57, c_56])).
% 4.71/1.80  tff(c_266, plain, (![D_38]: (D_38='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_38)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_38, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_257, c_147])).
% 4.71/1.80  tff(c_275, plain, (![D_38]: (D_38='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_38)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_38, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_36, c_266])).
% 4.71/1.80  tff(c_276, plain, (![D_38]: (D_38='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_38)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_38, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_57, c_275])).
% 4.71/1.80  tff(c_494, plain, (~r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_276])).
% 4.71/1.80  tff(c_103, plain, (![A_56, B_57, C_58]: (k1_relset_1(A_56, B_57, C_58)=k1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.71/1.80  tff(c_111, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_103])).
% 4.71/1.80  tff(c_124, plain, (![A_61, B_62, C_63]: (m1_subset_1(k1_relset_1(A_61, B_62, C_63), k1_zfmisc_1(A_61)) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.71/1.80  tff(c_139, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_111, c_124])).
% 4.71/1.80  tff(c_146, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_139])).
% 4.71/1.80  tff(c_95, plain, (![A_54]: (r2_hidden('#skF_2'(A_54), k1_relat_1(A_54)) | v2_funct_1(A_54) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.71/1.80  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.71/1.80  tff(c_560, plain, (![A_110, A_111]: (r2_hidden('#skF_2'(A_110), A_111) | ~m1_subset_1(k1_relat_1(A_110), k1_zfmisc_1(A_111)) | v2_funct_1(A_110) | ~v1_funct_1(A_110) | ~v1_relat_1(A_110))), inference(resolution, [status(thm)], [c_95, c_2])).
% 4.71/1.80  tff(c_578, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_146, c_560])).
% 4.71/1.80  tff(c_596, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_36, c_578])).
% 4.71/1.80  tff(c_598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_494, c_596])).
% 4.71/1.80  tff(c_600, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_276])).
% 4.71/1.80  tff(c_263, plain, (![C_37]: (C_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_37, '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_257, c_147])).
% 4.71/1.80  tff(c_272, plain, (![C_37]: (C_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_37, '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_36, c_263])).
% 4.71/1.80  tff(c_273, plain, (![C_37]: (C_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_37, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_57, c_272])).
% 4.71/1.80  tff(c_651, plain, (![C_37]: (C_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(C_37, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_600, c_273])).
% 4.71/1.80  tff(c_654, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | ~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_651])).
% 4.71/1.80  tff(c_655, plain, (~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_83, c_654])).
% 4.71/1.80  tff(c_99, plain, (![A_55]: (r2_hidden('#skF_1'(A_55), k1_relat_1(A_55)) | v2_funct_1(A_55) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.71/1.80  tff(c_749, plain, (![A_124, A_125]: (r2_hidden('#skF_1'(A_124), A_125) | ~m1_subset_1(k1_relat_1(A_124), k1_zfmisc_1(A_125)) | v2_funct_1(A_124) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(resolution, [status(thm)], [c_99, c_2])).
% 4.71/1.80  tff(c_764, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_146, c_749])).
% 4.71/1.80  tff(c_779, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_36, c_764])).
% 4.71/1.80  tff(c_781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_655, c_779])).
% 4.71/1.80  tff(c_782, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_38])).
% 4.71/1.80  tff(c_34, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.71/1.80  tff(c_783, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_38])).
% 4.71/1.80  tff(c_42, plain, (r2_hidden('#skF_6', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.71/1.80  tff(c_787, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_783, c_42])).
% 4.71/1.80  tff(c_1757, plain, (![D_236, C_237, B_238, A_239]: (k1_funct_1(k2_funct_1(D_236), k1_funct_1(D_236, C_237))=C_237 | k1_xboole_0=B_238 | ~r2_hidden(C_237, A_239) | ~v2_funct_1(D_236) | ~m1_subset_1(D_236, k1_zfmisc_1(k2_zfmisc_1(A_239, B_238))) | ~v1_funct_2(D_236, A_239, B_238) | ~v1_funct_1(D_236))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.71/1.80  tff(c_1848, plain, (![D_245, B_246]: (k1_funct_1(k2_funct_1(D_245), k1_funct_1(D_245, '#skF_6'))='#skF_6' | k1_xboole_0=B_246 | ~v2_funct_1(D_245) | ~m1_subset_1(D_245, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_246))) | ~v1_funct_2(D_245, '#skF_3', B_246) | ~v1_funct_1(D_245))), inference(resolution, [status(thm)], [c_787, c_1757])).
% 4.71/1.80  tff(c_1868, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_1848])).
% 4.71/1.80  tff(c_1880, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_783, c_1868])).
% 4.71/1.80  tff(c_1882, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1880])).
% 4.71/1.80  tff(c_4, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.71/1.80  tff(c_1909, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_1882, c_4])).
% 4.71/1.80  tff(c_44, plain, (r2_hidden('#skF_5', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.71/1.80  tff(c_789, plain, (r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_783, c_44])).
% 4.71/1.80  tff(c_814, plain, (![C_132, A_133, B_134]: (r2_hidden(C_132, A_133) | ~r2_hidden(C_132, B_134) | ~m1_subset_1(B_134, k1_zfmisc_1(A_133)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.71/1.80  tff(c_819, plain, (![A_133]: (r2_hidden('#skF_5', A_133) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_133)))), inference(resolution, [status(thm)], [c_789, c_814])).
% 4.71/1.80  tff(c_1923, plain, (![A_133]: (r2_hidden('#skF_5', A_133))), inference(demodulation, [status(thm), theory('equality')], [c_1909, c_819])).
% 4.71/1.80  tff(c_796, plain, (![B_129, A_130]: (v1_relat_1(B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(A_130)) | ~v1_relat_1(A_130))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.71/1.80  tff(c_799, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_796])).
% 4.71/1.80  tff(c_805, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_799])).
% 4.71/1.80  tff(c_40, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.71/1.80  tff(c_791, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_783, c_40])).
% 4.71/1.80  tff(c_1612, plain, (![B_221, A_222]: (k1_funct_1(k2_funct_1(B_221), k1_funct_1(B_221, A_222))=A_222 | ~r2_hidden(A_222, k1_relat_1(B_221)) | ~v2_funct_1(B_221) | ~v1_funct_1(B_221) | ~v1_relat_1(B_221))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.71/1.80  tff(c_1633, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5' | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_791, c_1612])).
% 4.71/1.80  tff(c_1637, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5' | ~r2_hidden('#skF_5', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_805, c_36, c_783, c_1633])).
% 4.71/1.80  tff(c_1638, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1637])).
% 4.71/1.80  tff(c_1961, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1923, c_1638])).
% 4.71/1.80  tff(c_1963, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1880])).
% 4.71/1.80  tff(c_1962, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1880])).
% 4.71/1.80  tff(c_1964, plain, (![D_253, B_254]: (k1_funct_1(k2_funct_1(D_253), k1_funct_1(D_253, '#skF_5'))='#skF_5' | k1_xboole_0=B_254 | ~v2_funct_1(D_253) | ~m1_subset_1(D_253, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_254))) | ~v1_funct_2(D_253, '#skF_3', B_254) | ~v1_funct_1(D_253))), inference(resolution, [status(thm)], [c_789, c_1757])).
% 4.71/1.80  tff(c_1984, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_1964])).
% 4.71/1.80  tff(c_1996, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_783, c_791, c_1984])).
% 4.71/1.80  tff(c_2021, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1962, c_1996])).
% 4.71/1.80  tff(c_2022, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1963, c_782, c_2021])).
% 4.71/1.80  tff(c_2023, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1637])).
% 4.71/1.80  tff(c_2202, plain, (![D_270, C_271, B_272, A_273]: (k1_funct_1(k2_funct_1(D_270), k1_funct_1(D_270, C_271))=C_271 | k1_xboole_0=B_272 | ~r2_hidden(C_271, A_273) | ~v2_funct_1(D_270) | ~m1_subset_1(D_270, k1_zfmisc_1(k2_zfmisc_1(A_273, B_272))) | ~v1_funct_2(D_270, A_273, B_272) | ~v1_funct_1(D_270))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.71/1.80  tff(c_2245, plain, (![D_276, B_277]: (k1_funct_1(k2_funct_1(D_276), k1_funct_1(D_276, '#skF_6'))='#skF_6' | k1_xboole_0=B_277 | ~v2_funct_1(D_276) | ~m1_subset_1(D_276, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_277))) | ~v1_funct_2(D_276, '#skF_3', B_277) | ~v1_funct_1(D_276))), inference(resolution, [status(thm)], [c_787, c_2202])).
% 4.71/1.80  tff(c_2262, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_2245])).
% 4.71/1.80  tff(c_2273, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_783, c_2023, c_2262])).
% 4.71/1.80  tff(c_2274, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_782, c_2273])).
% 4.71/1.80  tff(c_2300, plain, (![A_5]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_2274, c_4])).
% 4.71/1.80  tff(c_820, plain, (![A_133]: (r2_hidden('#skF_6', A_133) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_133)))), inference(resolution, [status(thm)], [c_787, c_814])).
% 4.71/1.80  tff(c_2307, plain, (![A_133]: (r2_hidden('#skF_6', A_133))), inference(demodulation, [status(thm), theory('equality')], [c_2300, c_820])).
% 4.71/1.80  tff(c_24, plain, (![B_22, A_21]: (k1_funct_1(k2_funct_1(B_22), k1_funct_1(B_22, A_21))=A_21 | ~r2_hidden(A_21, k1_relat_1(B_22)) | ~v2_funct_1(B_22) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.71/1.80  tff(c_2039, plain, ('#skF_5'='#skF_6' | ~r2_hidden('#skF_6', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2023, c_24])).
% 4.71/1.80  tff(c_2046, plain, ('#skF_5'='#skF_6' | ~r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_805, c_36, c_783, c_2039])).
% 4.71/1.80  tff(c_2047, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_782, c_2046])).
% 4.71/1.80  tff(c_2339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2307, c_2047])).
% 4.71/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.80  
% 4.71/1.80  Inference rules
% 4.71/1.80  ----------------------
% 4.71/1.80  #Ref     : 6
% 4.71/1.80  #Sup     : 428
% 4.71/1.80  #Fact    : 0
% 4.71/1.80  #Define  : 0
% 4.71/1.80  #Split   : 45
% 4.71/1.80  #Chain   : 0
% 4.71/1.80  #Close   : 0
% 4.71/1.80  
% 4.71/1.80  Ordering : KBO
% 4.71/1.80  
% 4.71/1.80  Simplification rules
% 4.71/1.80  ----------------------
% 4.71/1.80  #Subsume      : 200
% 4.71/1.80  #Demod        : 361
% 4.71/1.80  #Tautology    : 140
% 4.71/1.80  #SimpNegUnit  : 151
% 4.71/1.80  #BackRed      : 197
% 4.71/1.80  
% 4.71/1.80  #Partial instantiations: 0
% 4.71/1.80  #Strategies tried      : 1
% 4.71/1.80  
% 4.71/1.80  Timing (in seconds)
% 4.71/1.80  ----------------------
% 4.71/1.80  Preprocessing        : 0.31
% 4.71/1.80  Parsing              : 0.16
% 4.81/1.80  CNF conversion       : 0.02
% 4.81/1.80  Main loop            : 0.71
% 4.81/1.80  Inferencing          : 0.23
% 4.81/1.80  Reduction            : 0.25
% 4.81/1.80  Demodulation         : 0.18
% 4.81/1.80  BG Simplification    : 0.03
% 4.81/1.80  Subsumption          : 0.14
% 4.81/1.80  Abstraction          : 0.03
% 4.81/1.80  MUC search           : 0.00
% 4.81/1.80  Cooper               : 0.00
% 4.81/1.80  Total                : 1.08
% 4.81/1.80  Index Insertion      : 0.00
% 4.81/1.80  Index Deletion       : 0.00
% 4.81/1.80  Index Matching       : 0.00
% 4.81/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
