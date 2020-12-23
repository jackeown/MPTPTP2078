%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:30 EST 2020

% Result     : Theorem 14.75s
% Output     : CNFRefutation 14.85s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 666 expanded)
%              Number of leaves         :   43 ( 249 expanded)
%              Depth                    :   12
%              Number of atoms          :  189 (2038 expanded)
%              Number of equality atoms :   60 ( 753 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_84,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_131,axiom,(
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

tff(f_95,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_82,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_3799,plain,(
    ! [A_241,B_242,C_243,D_244] :
      ( k7_relset_1(A_241,B_242,C_243,D_244) = k9_relat_1(C_243,D_244)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_3829,plain,(
    ! [D_244] : k7_relset_1('#skF_7','#skF_8','#skF_10',D_244) = k9_relat_1('#skF_10',D_244) ),
    inference(resolution,[status(thm)],[c_82,c_3799])).

tff(c_80,plain,(
    r2_hidden('#skF_11',k7_relset_1('#skF_7','#skF_8','#skF_10','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_164,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_7','#skF_8','#skF_10','#skF_9')) ),
    inference(resolution,[status(thm)],[c_80,c_2])).

tff(c_3833,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3829,c_164])).

tff(c_38,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(A_30,B_31)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_163,plain,(
    m1_subset_1('#skF_11',k7_relset_1('#skF_7','#skF_8','#skF_10','#skF_9')) ),
    inference(resolution,[status(thm)],[c_80,c_38])).

tff(c_3832,plain,(
    m1_subset_1('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3829,c_163])).

tff(c_46,plain,(
    ! [A_38,B_39] : v1_relat_1(k2_zfmisc_1(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_171,plain,(
    ! [B_81,A_82] :
      ( v1_relat_1(B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_82))
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_178,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_82,c_171])).

tff(c_184,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_178])).

tff(c_3834,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3829,c_80])).

tff(c_84,plain,(
    v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_901,plain,(
    ! [A_135,B_136,C_137] :
      ( k1_relset_1(A_135,B_136,C_137) = k1_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k2_zfmisc_1(A_135,B_136))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_918,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_82,c_901])).

tff(c_6379,plain,(
    ! [B_303,A_304,C_305] :
      ( k1_xboole_0 = B_303
      | k1_relset_1(A_304,B_303,C_305) = A_304
      | ~ v1_funct_2(C_305,A_304,B_303)
      | ~ m1_subset_1(C_305,k1_zfmisc_1(k2_zfmisc_1(A_304,B_303))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_6402,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_82,c_6379])).

tff(c_6419,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_918,c_6402])).

tff(c_6421,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_6419])).

tff(c_3356,plain,(
    ! [A_230,B_231,C_232] :
      ( r2_hidden('#skF_6'(A_230,B_231,C_232),k1_relat_1(C_232))
      | ~ r2_hidden(A_230,k9_relat_1(C_232,B_231))
      | ~ v1_relat_1(C_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_24928,plain,(
    ! [A_526,B_527,C_528] :
      ( m1_subset_1('#skF_6'(A_526,B_527,C_528),k1_relat_1(C_528))
      | ~ r2_hidden(A_526,k9_relat_1(C_528,B_527))
      | ~ v1_relat_1(C_528) ) ),
    inference(resolution,[status(thm)],[c_3356,c_38])).

tff(c_24931,plain,(
    ! [A_526,B_527] :
      ( m1_subset_1('#skF_6'(A_526,B_527,'#skF_10'),'#skF_7')
      | ~ r2_hidden(A_526,k9_relat_1('#skF_10',B_527))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6421,c_24928])).

tff(c_34526,plain,(
    ! [A_646,B_647] :
      ( m1_subset_1('#skF_6'(A_646,B_647,'#skF_10'),'#skF_7')
      | ~ r2_hidden(A_646,k9_relat_1('#skF_10',B_647)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_24931])).

tff(c_34643,plain,(
    m1_subset_1('#skF_6'('#skF_11','#skF_9','#skF_10'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_3834,c_34526])).

tff(c_40,plain,(
    ! [A_32,B_33] :
      ( r2_hidden(A_32,B_33)
      | v1_xboole_0(B_33)
      | ~ m1_subset_1(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2870,plain,(
    ! [A_214,B_215,C_216] :
      ( r2_hidden('#skF_6'(A_214,B_215,C_216),B_215)
      | ~ r2_hidden(A_214,k9_relat_1(C_216,B_215))
      | ~ v1_relat_1(C_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_78,plain,(
    ! [F_63] :
      ( k1_funct_1('#skF_10',F_63) != '#skF_11'
      | ~ r2_hidden(F_63,'#skF_9')
      | ~ m1_subset_1(F_63,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_3463,plain,(
    ! [A_236,C_237] :
      ( k1_funct_1('#skF_10','#skF_6'(A_236,'#skF_9',C_237)) != '#skF_11'
      | ~ m1_subset_1('#skF_6'(A_236,'#skF_9',C_237),'#skF_7')
      | ~ r2_hidden(A_236,k9_relat_1(C_237,'#skF_9'))
      | ~ v1_relat_1(C_237) ) ),
    inference(resolution,[status(thm)],[c_2870,c_78])).

tff(c_3517,plain,(
    ! [A_32,C_237] :
      ( k1_funct_1('#skF_10','#skF_6'(A_32,'#skF_9',C_237)) != '#skF_11'
      | ~ m1_subset_1('#skF_6'(A_32,'#skF_9',C_237),'#skF_7')
      | ~ v1_relat_1(C_237)
      | v1_xboole_0(k9_relat_1(C_237,'#skF_9'))
      | ~ m1_subset_1(A_32,k9_relat_1(C_237,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_40,c_3463])).

tff(c_34657,plain,
    ( k1_funct_1('#skF_10','#skF_6'('#skF_11','#skF_9','#skF_10')) != '#skF_11'
    | ~ v1_relat_1('#skF_10')
    | v1_xboole_0(k9_relat_1('#skF_10','#skF_9'))
    | ~ m1_subset_1('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(resolution,[status(thm)],[c_34643,c_3517])).

tff(c_34663,plain,
    ( k1_funct_1('#skF_10','#skF_6'('#skF_11','#skF_9','#skF_10')) != '#skF_11'
    | v1_xboole_0(k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3832,c_184,c_34657])).

tff(c_34664,plain,(
    k1_funct_1('#skF_10','#skF_6'('#skF_11','#skF_9','#skF_10')) != '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_3833,c_34663])).

tff(c_86,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_4305,plain,(
    ! [A_250,B_251,C_252] :
      ( r2_hidden(k4_tarski('#skF_6'(A_250,B_251,C_252),A_250),C_252)
      | ~ r2_hidden(A_250,k9_relat_1(C_252,B_251))
      | ~ v1_relat_1(C_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_58,plain,(
    ! [C_48,A_46,B_47] :
      ( k1_funct_1(C_48,A_46) = B_47
      | ~ r2_hidden(k4_tarski(A_46,B_47),C_48)
      | ~ v1_funct_1(C_48)
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_34668,plain,(
    ! [C_648,A_649,B_650] :
      ( k1_funct_1(C_648,'#skF_6'(A_649,B_650,C_648)) = A_649
      | ~ v1_funct_1(C_648)
      | ~ r2_hidden(A_649,k9_relat_1(C_648,B_650))
      | ~ v1_relat_1(C_648) ) ),
    inference(resolution,[status(thm)],[c_4305,c_58])).

tff(c_34731,plain,
    ( k1_funct_1('#skF_10','#skF_6'('#skF_11','#skF_9','#skF_10')) = '#skF_11'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_3834,c_34668])).

tff(c_34781,plain,(
    k1_funct_1('#skF_10','#skF_6'('#skF_11','#skF_9','#skF_10')) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_86,c_34731])).

tff(c_34783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34664,c_34781])).

tff(c_34784,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_6419])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34852,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34784,c_6])).

tff(c_30,plain,(
    ! [A_26] : k2_zfmisc_1(A_26,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34850,plain,(
    ! [A_26] : k2_zfmisc_1(A_26,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34784,c_34784,c_30])).

tff(c_35104,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34850,c_82])).

tff(c_68,plain,(
    ! [C_58,A_56] :
      ( k1_xboole_0 = C_58
      | ~ v1_funct_2(C_58,A_56,k1_xboole_0)
      | k1_xboole_0 = A_56
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_89,plain,(
    ! [C_58,A_56] :
      ( k1_xboole_0 = C_58
      | ~ v1_funct_2(C_58,A_56,k1_xboole_0)
      | k1_xboole_0 = A_56
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_68])).

tff(c_38593,plain,(
    ! [C_741,A_742] :
      ( C_741 = '#skF_8'
      | ~ v1_funct_2(C_741,A_742,'#skF_8')
      | A_742 = '#skF_8'
      | ~ m1_subset_1(C_741,k1_zfmisc_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34784,c_34784,c_34784,c_34784,c_89])).

tff(c_38597,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_7' = '#skF_8'
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_84,c_38593])).

tff(c_38604,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35104,c_38597])).

tff(c_38605,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_38604])).

tff(c_34785,plain,(
    k1_relat_1('#skF_10') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_6419])).

tff(c_38614,plain,(
    k1_relat_1('#skF_10') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38605,c_34785])).

tff(c_914,plain,(
    ! [A_26,C_137] :
      ( k1_relset_1(A_26,k1_xboole_0,C_137) = k1_relat_1(C_137)
      | ~ m1_subset_1(C_137,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_901])).

tff(c_36045,plain,(
    ! [A_684,C_685] :
      ( k1_relset_1(A_684,'#skF_8',C_685) = k1_relat_1(C_685)
      | ~ m1_subset_1(C_685,k1_zfmisc_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34784,c_34784,c_914])).

tff(c_36065,plain,(
    ! [A_684] : k1_relset_1(A_684,'#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_35104,c_36045])).

tff(c_38625,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38605,c_84])).

tff(c_32,plain,(
    ! [B_27] : k2_zfmisc_1(k1_xboole_0,B_27) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_74,plain,(
    ! [B_57,C_58] :
      ( k1_relset_1(k1_xboole_0,B_57,C_58) = k1_xboole_0
      | ~ v1_funct_2(C_58,k1_xboole_0,B_57)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_87,plain,(
    ! [B_57,C_58] :
      ( k1_relset_1(k1_xboole_0,B_57,C_58) = k1_xboole_0
      | ~ v1_funct_2(C_58,k1_xboole_0,B_57)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_74])).

tff(c_40533,plain,(
    ! [B_785,C_786] :
      ( k1_relset_1('#skF_8',B_785,C_786) = '#skF_8'
      | ~ v1_funct_2(C_786,'#skF_8',B_785)
      | ~ m1_subset_1(C_786,k1_zfmisc_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34784,c_34784,c_34784,c_34784,c_87])).

tff(c_40535,plain,
    ( k1_relset_1('#skF_8','#skF_8','#skF_10') = '#skF_8'
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_38625,c_40533])).

tff(c_40541,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35104,c_36065,c_40535])).

tff(c_40543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38614,c_40541])).

tff(c_40544,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_38604])).

tff(c_5816,plain,(
    ! [C_281,A_282,B_283] :
      ( ~ v1_xboole_0(C_281)
      | ~ r2_hidden(A_282,k9_relat_1(C_281,B_283))
      | ~ v1_relat_1(C_281) ) ),
    inference(resolution,[status(thm)],[c_4305,c_2])).

tff(c_5842,plain,
    ( ~ v1_xboole_0('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_3834,c_5816])).

tff(c_5902,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_5842])).

tff(c_40564,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40544,c_5902])).

tff(c_40593,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34852,c_40564])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:54:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.75/6.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.75/6.22  
% 14.75/6.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.75/6.22  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 14.75/6.22  
% 14.75/6.22  %Foreground sorts:
% 14.75/6.22  
% 14.75/6.22  
% 14.75/6.22  %Background operators:
% 14.75/6.22  
% 14.75/6.22  
% 14.75/6.22  %Foreground operators:
% 14.75/6.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.75/6.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.75/6.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.75/6.22  tff('#skF_11', type, '#skF_11': $i).
% 14.75/6.22  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 14.75/6.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 14.75/6.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 14.75/6.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.75/6.22  tff('#skF_7', type, '#skF_7': $i).
% 14.75/6.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 14.75/6.22  tff('#skF_10', type, '#skF_10': $i).
% 14.75/6.22  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 14.75/6.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.75/6.22  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 14.75/6.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 14.75/6.22  tff('#skF_9', type, '#skF_9': $i).
% 14.75/6.22  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 14.75/6.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.75/6.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 14.75/6.22  tff('#skF_8', type, '#skF_8': $i).
% 14.75/6.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.75/6.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 14.75/6.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.75/6.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.75/6.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.75/6.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.75/6.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.75/6.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.75/6.22  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 14.75/6.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.75/6.22  
% 14.85/6.24  tff(f_150, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 14.85/6.24  tff(f_113, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 14.85/6.24  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 14.85/6.24  tff(f_65, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 14.85/6.24  tff(f_84, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 14.85/6.24  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 14.85/6.24  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 14.85/6.24  tff(f_131, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 14.85/6.24  tff(f_95, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 14.85/6.24  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 14.85/6.24  tff(f_105, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 14.85/6.24  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 14.85/6.24  tff(f_56, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 14.85/6.24  tff(c_82, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 14.85/6.24  tff(c_3799, plain, (![A_241, B_242, C_243, D_244]: (k7_relset_1(A_241, B_242, C_243, D_244)=k9_relat_1(C_243, D_244) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_241, B_242))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 14.85/6.24  tff(c_3829, plain, (![D_244]: (k7_relset_1('#skF_7', '#skF_8', '#skF_10', D_244)=k9_relat_1('#skF_10', D_244))), inference(resolution, [status(thm)], [c_82, c_3799])).
% 14.85/6.24  tff(c_80, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_7', '#skF_8', '#skF_10', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 14.85/6.24  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.85/6.24  tff(c_164, plain, (~v1_xboole_0(k7_relset_1('#skF_7', '#skF_8', '#skF_10', '#skF_9'))), inference(resolution, [status(thm)], [c_80, c_2])).
% 14.85/6.24  tff(c_3833, plain, (~v1_xboole_0(k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_3829, c_164])).
% 14.85/6.24  tff(c_38, plain, (![A_30, B_31]: (m1_subset_1(A_30, B_31) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_65])).
% 14.85/6.24  tff(c_163, plain, (m1_subset_1('#skF_11', k7_relset_1('#skF_7', '#skF_8', '#skF_10', '#skF_9'))), inference(resolution, [status(thm)], [c_80, c_38])).
% 14.85/6.24  tff(c_3832, plain, (m1_subset_1('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_3829, c_163])).
% 14.85/6.24  tff(c_46, plain, (![A_38, B_39]: (v1_relat_1(k2_zfmisc_1(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 14.85/6.24  tff(c_171, plain, (![B_81, A_82]: (v1_relat_1(B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_82)) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.85/6.24  tff(c_178, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_82, c_171])).
% 14.85/6.24  tff(c_184, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_178])).
% 14.85/6.24  tff(c_3834, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_3829, c_80])).
% 14.85/6.24  tff(c_84, plain, (v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_150])).
% 14.85/6.24  tff(c_901, plain, (![A_135, B_136, C_137]: (k1_relset_1(A_135, B_136, C_137)=k1_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 14.85/6.24  tff(c_918, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_82, c_901])).
% 14.85/6.24  tff(c_6379, plain, (![B_303, A_304, C_305]: (k1_xboole_0=B_303 | k1_relset_1(A_304, B_303, C_305)=A_304 | ~v1_funct_2(C_305, A_304, B_303) | ~m1_subset_1(C_305, k1_zfmisc_1(k2_zfmisc_1(A_304, B_303))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 14.85/6.24  tff(c_6402, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_82, c_6379])).
% 14.85/6.24  tff(c_6419, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_918, c_6402])).
% 14.85/6.24  tff(c_6421, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_6419])).
% 14.85/6.24  tff(c_3356, plain, (![A_230, B_231, C_232]: (r2_hidden('#skF_6'(A_230, B_231, C_232), k1_relat_1(C_232)) | ~r2_hidden(A_230, k9_relat_1(C_232, B_231)) | ~v1_relat_1(C_232))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.85/6.24  tff(c_24928, plain, (![A_526, B_527, C_528]: (m1_subset_1('#skF_6'(A_526, B_527, C_528), k1_relat_1(C_528)) | ~r2_hidden(A_526, k9_relat_1(C_528, B_527)) | ~v1_relat_1(C_528))), inference(resolution, [status(thm)], [c_3356, c_38])).
% 14.85/6.24  tff(c_24931, plain, (![A_526, B_527]: (m1_subset_1('#skF_6'(A_526, B_527, '#skF_10'), '#skF_7') | ~r2_hidden(A_526, k9_relat_1('#skF_10', B_527)) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_6421, c_24928])).
% 14.85/6.24  tff(c_34526, plain, (![A_646, B_647]: (m1_subset_1('#skF_6'(A_646, B_647, '#skF_10'), '#skF_7') | ~r2_hidden(A_646, k9_relat_1('#skF_10', B_647)))), inference(demodulation, [status(thm), theory('equality')], [c_184, c_24931])).
% 14.85/6.24  tff(c_34643, plain, (m1_subset_1('#skF_6'('#skF_11', '#skF_9', '#skF_10'), '#skF_7')), inference(resolution, [status(thm)], [c_3834, c_34526])).
% 14.85/6.24  tff(c_40, plain, (![A_32, B_33]: (r2_hidden(A_32, B_33) | v1_xboole_0(B_33) | ~m1_subset_1(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_71])).
% 14.85/6.24  tff(c_2870, plain, (![A_214, B_215, C_216]: (r2_hidden('#skF_6'(A_214, B_215, C_216), B_215) | ~r2_hidden(A_214, k9_relat_1(C_216, B_215)) | ~v1_relat_1(C_216))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.85/6.24  tff(c_78, plain, (![F_63]: (k1_funct_1('#skF_10', F_63)!='#skF_11' | ~r2_hidden(F_63, '#skF_9') | ~m1_subset_1(F_63, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 14.85/6.24  tff(c_3463, plain, (![A_236, C_237]: (k1_funct_1('#skF_10', '#skF_6'(A_236, '#skF_9', C_237))!='#skF_11' | ~m1_subset_1('#skF_6'(A_236, '#skF_9', C_237), '#skF_7') | ~r2_hidden(A_236, k9_relat_1(C_237, '#skF_9')) | ~v1_relat_1(C_237))), inference(resolution, [status(thm)], [c_2870, c_78])).
% 14.85/6.24  tff(c_3517, plain, (![A_32, C_237]: (k1_funct_1('#skF_10', '#skF_6'(A_32, '#skF_9', C_237))!='#skF_11' | ~m1_subset_1('#skF_6'(A_32, '#skF_9', C_237), '#skF_7') | ~v1_relat_1(C_237) | v1_xboole_0(k9_relat_1(C_237, '#skF_9')) | ~m1_subset_1(A_32, k9_relat_1(C_237, '#skF_9')))), inference(resolution, [status(thm)], [c_40, c_3463])).
% 14.85/6.24  tff(c_34657, plain, (k1_funct_1('#skF_10', '#skF_6'('#skF_11', '#skF_9', '#skF_10'))!='#skF_11' | ~v1_relat_1('#skF_10') | v1_xboole_0(k9_relat_1('#skF_10', '#skF_9')) | ~m1_subset_1('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(resolution, [status(thm)], [c_34643, c_3517])).
% 14.85/6.24  tff(c_34663, plain, (k1_funct_1('#skF_10', '#skF_6'('#skF_11', '#skF_9', '#skF_10'))!='#skF_11' | v1_xboole_0(k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_3832, c_184, c_34657])).
% 14.85/6.24  tff(c_34664, plain, (k1_funct_1('#skF_10', '#skF_6'('#skF_11', '#skF_9', '#skF_10'))!='#skF_11'), inference(negUnitSimplification, [status(thm)], [c_3833, c_34663])).
% 14.85/6.24  tff(c_86, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_150])).
% 14.85/6.24  tff(c_4305, plain, (![A_250, B_251, C_252]: (r2_hidden(k4_tarski('#skF_6'(A_250, B_251, C_252), A_250), C_252) | ~r2_hidden(A_250, k9_relat_1(C_252, B_251)) | ~v1_relat_1(C_252))), inference(cnfTransformation, [status(thm)], [f_95])).
% 14.85/6.24  tff(c_58, plain, (![C_48, A_46, B_47]: (k1_funct_1(C_48, A_46)=B_47 | ~r2_hidden(k4_tarski(A_46, B_47), C_48) | ~v1_funct_1(C_48) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_105])).
% 14.85/6.24  tff(c_34668, plain, (![C_648, A_649, B_650]: (k1_funct_1(C_648, '#skF_6'(A_649, B_650, C_648))=A_649 | ~v1_funct_1(C_648) | ~r2_hidden(A_649, k9_relat_1(C_648, B_650)) | ~v1_relat_1(C_648))), inference(resolution, [status(thm)], [c_4305, c_58])).
% 14.85/6.24  tff(c_34731, plain, (k1_funct_1('#skF_10', '#skF_6'('#skF_11', '#skF_9', '#skF_10'))='#skF_11' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_3834, c_34668])).
% 14.85/6.24  tff(c_34781, plain, (k1_funct_1('#skF_10', '#skF_6'('#skF_11', '#skF_9', '#skF_10'))='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_184, c_86, c_34731])).
% 14.85/6.24  tff(c_34783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34664, c_34781])).
% 14.85/6.24  tff(c_34784, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_6419])).
% 14.85/6.24  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.85/6.24  tff(c_34852, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34784, c_6])).
% 14.85/6.24  tff(c_30, plain, (![A_26]: (k2_zfmisc_1(A_26, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.85/6.24  tff(c_34850, plain, (![A_26]: (k2_zfmisc_1(A_26, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34784, c_34784, c_30])).
% 14.85/6.24  tff(c_35104, plain, (m1_subset_1('#skF_10', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_34850, c_82])).
% 14.85/6.24  tff(c_68, plain, (![C_58, A_56]: (k1_xboole_0=C_58 | ~v1_funct_2(C_58, A_56, k1_xboole_0) | k1_xboole_0=A_56 | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 14.85/6.24  tff(c_89, plain, (![C_58, A_56]: (k1_xboole_0=C_58 | ~v1_funct_2(C_58, A_56, k1_xboole_0) | k1_xboole_0=A_56 | ~m1_subset_1(C_58, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_68])).
% 14.85/6.24  tff(c_38593, plain, (![C_741, A_742]: (C_741='#skF_8' | ~v1_funct_2(C_741, A_742, '#skF_8') | A_742='#skF_8' | ~m1_subset_1(C_741, k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_34784, c_34784, c_34784, c_34784, c_89])).
% 14.85/6.24  tff(c_38597, plain, ('#skF_10'='#skF_8' | '#skF_7'='#skF_8' | ~m1_subset_1('#skF_10', k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_84, c_38593])).
% 14.85/6.24  tff(c_38604, plain, ('#skF_10'='#skF_8' | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_35104, c_38597])).
% 14.85/6.24  tff(c_38605, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_38604])).
% 14.85/6.24  tff(c_34785, plain, (k1_relat_1('#skF_10')!='#skF_7'), inference(splitRight, [status(thm)], [c_6419])).
% 14.85/6.24  tff(c_38614, plain, (k1_relat_1('#skF_10')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_38605, c_34785])).
% 14.85/6.24  tff(c_914, plain, (![A_26, C_137]: (k1_relset_1(A_26, k1_xboole_0, C_137)=k1_relat_1(C_137) | ~m1_subset_1(C_137, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_901])).
% 14.85/6.24  tff(c_36045, plain, (![A_684, C_685]: (k1_relset_1(A_684, '#skF_8', C_685)=k1_relat_1(C_685) | ~m1_subset_1(C_685, k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_34784, c_34784, c_914])).
% 14.85/6.24  tff(c_36065, plain, (![A_684]: (k1_relset_1(A_684, '#skF_8', '#skF_10')=k1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_35104, c_36045])).
% 14.85/6.24  tff(c_38625, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_38605, c_84])).
% 14.85/6.24  tff(c_32, plain, (![B_27]: (k2_zfmisc_1(k1_xboole_0, B_27)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 14.85/6.24  tff(c_74, plain, (![B_57, C_58]: (k1_relset_1(k1_xboole_0, B_57, C_58)=k1_xboole_0 | ~v1_funct_2(C_58, k1_xboole_0, B_57) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_57))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 14.85/6.24  tff(c_87, plain, (![B_57, C_58]: (k1_relset_1(k1_xboole_0, B_57, C_58)=k1_xboole_0 | ~v1_funct_2(C_58, k1_xboole_0, B_57) | ~m1_subset_1(C_58, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_74])).
% 14.85/6.24  tff(c_40533, plain, (![B_785, C_786]: (k1_relset_1('#skF_8', B_785, C_786)='#skF_8' | ~v1_funct_2(C_786, '#skF_8', B_785) | ~m1_subset_1(C_786, k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_34784, c_34784, c_34784, c_34784, c_87])).
% 14.85/6.24  tff(c_40535, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_10')='#skF_8' | ~m1_subset_1('#skF_10', k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_38625, c_40533])).
% 14.85/6.24  tff(c_40541, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_35104, c_36065, c_40535])).
% 14.85/6.24  tff(c_40543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38614, c_40541])).
% 14.85/6.24  tff(c_40544, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_38604])).
% 14.85/6.24  tff(c_5816, plain, (![C_281, A_282, B_283]: (~v1_xboole_0(C_281) | ~r2_hidden(A_282, k9_relat_1(C_281, B_283)) | ~v1_relat_1(C_281))), inference(resolution, [status(thm)], [c_4305, c_2])).
% 14.85/6.24  tff(c_5842, plain, (~v1_xboole_0('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_3834, c_5816])).
% 14.85/6.24  tff(c_5902, plain, (~v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_184, c_5842])).
% 14.85/6.24  tff(c_40564, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40544, c_5902])).
% 14.85/6.24  tff(c_40593, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34852, c_40564])).
% 14.85/6.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.85/6.24  
% 14.85/6.24  Inference rules
% 14.85/6.24  ----------------------
% 14.85/6.24  #Ref     : 0
% 14.85/6.24  #Sup     : 10170
% 14.85/6.24  #Fact    : 0
% 14.85/6.24  #Define  : 0
% 14.85/6.24  #Split   : 24
% 14.85/6.24  #Chain   : 0
% 14.85/6.24  #Close   : 0
% 14.85/6.24  
% 14.85/6.24  Ordering : KBO
% 14.85/6.24  
% 14.85/6.24  Simplification rules
% 14.85/6.24  ----------------------
% 14.85/6.24  #Subsume      : 2739
% 14.85/6.24  #Demod        : 10659
% 14.85/6.24  #Tautology    : 4407
% 14.85/6.24  #SimpNegUnit  : 447
% 14.85/6.24  #BackRed      : 135
% 14.85/6.24  
% 14.85/6.24  #Partial instantiations: 0
% 14.85/6.24  #Strategies tried      : 1
% 14.85/6.24  
% 14.85/6.24  Timing (in seconds)
% 14.85/6.24  ----------------------
% 14.85/6.24  Preprocessing        : 0.34
% 14.85/6.24  Parsing              : 0.17
% 14.85/6.24  CNF conversion       : 0.03
% 14.85/6.24  Main loop            : 5.08
% 14.85/6.24  Inferencing          : 1.07
% 14.85/6.24  Reduction            : 1.50
% 14.85/6.24  Demodulation         : 1.05
% 14.85/6.24  BG Simplification    : 0.11
% 14.85/6.24  Subsumption          : 2.09
% 14.85/6.24  Abstraction          : 0.19
% 14.85/6.24  MUC search           : 0.00
% 14.85/6.24  Cooper               : 0.00
% 14.85/6.24  Total                : 5.46
% 14.85/6.24  Index Insertion      : 0.00
% 14.85/6.24  Index Deletion       : 0.00
% 14.85/6.24  Index Matching       : 0.00
% 14.85/6.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
