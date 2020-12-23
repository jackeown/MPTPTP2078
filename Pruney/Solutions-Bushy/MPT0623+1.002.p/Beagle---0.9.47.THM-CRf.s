%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0623+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:36 EST 2020

% Result     : Theorem 10.17s
% Output     : CNFRefutation 10.38s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 299 expanded)
%              Number of leaves         :   36 ( 120 expanded)
%              Depth                    :   16
%              Number of atoms          :  159 ( 762 expanded)
%              Number of equality atoms :   43 ( 259 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > o_1_0_funct_1 > k2_relat_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_1_0_funct_1,type,(
    o_1_0_funct_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_57,axiom,(
    ! [A] : m1_subset_1(o_1_0_funct_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_1_0_funct_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_77,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = B
      & ! [D] :
          ( r2_hidden(D,B)
         => k1_funct_1(C,D) = o_1_0_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e1_27_1__funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
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

tff(f_89,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_28,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_85,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(c_30,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_32,plain,(
    ! [A_48] : m1_subset_1(o_1_0_funct_1(A_48),A_48) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_46,plain,(
    ! [A_58,B_59] :
      ( r2_hidden(A_58,B_59)
      | v1_xboole_0(B_59)
      | ~ m1_subset_1(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_44,plain,(
    ! [A_51,B_52] : v1_relat_1('#skF_6'(A_51,B_52)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_42,plain,(
    ! [A_51,B_52] : v1_funct_1('#skF_6'(A_51,B_52)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,(
    ! [A_51,B_52] : k1_relat_1('#skF_6'(A_51,B_52)) = B_52 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_294,plain,(
    ! [A_92,B_93] :
      ( ~ r2_hidden('#skF_1'(A_92,B_93),B_93)
      | r1_tarski(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_299,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_10,c_294])).

tff(c_603,plain,(
    ! [A_133,C_134] :
      ( r2_hidden('#skF_5'(A_133,k2_relat_1(A_133),C_134),k1_relat_1(A_133))
      | ~ r2_hidden(C_134,k2_relat_1(A_133))
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_630,plain,(
    ! [A_133,C_134,B_4] :
      ( r2_hidden('#skF_5'(A_133,k2_relat_1(A_133),C_134),B_4)
      | ~ r1_tarski(k1_relat_1(A_133),B_4)
      | ~ r2_hidden(C_134,k2_relat_1(A_133))
      | ~ v1_funct_1(A_133)
      | ~ v1_relat_1(A_133) ) ),
    inference(resolution,[status(thm)],[c_603,c_6])).

tff(c_710,plain,(
    ! [A_154,C_155] :
      ( k1_funct_1(A_154,'#skF_5'(A_154,k2_relat_1(A_154),C_155)) = C_155
      | ~ r2_hidden(C_155,k2_relat_1(A_154))
      | ~ v1_funct_1(A_154)
      | ~ v1_relat_1(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_38,plain,(
    ! [A_51,B_52,D_57] :
      ( k1_funct_1('#skF_6'(A_51,B_52),D_57) = o_1_0_funct_1(A_51)
      | ~ r2_hidden(D_57,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_720,plain,(
    ! [A_51,C_155,B_52] :
      ( o_1_0_funct_1(A_51) = C_155
      | ~ r2_hidden('#skF_5'('#skF_6'(A_51,B_52),k2_relat_1('#skF_6'(A_51,B_52)),C_155),B_52)
      | ~ r2_hidden(C_155,k2_relat_1('#skF_6'(A_51,B_52)))
      | ~ v1_funct_1('#skF_6'(A_51,B_52))
      | ~ v1_relat_1('#skF_6'(A_51,B_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_710,c_38])).

tff(c_4219,plain,(
    ! [A_394,C_395,B_396] :
      ( o_1_0_funct_1(A_394) = C_395
      | ~ r2_hidden('#skF_5'('#skF_6'(A_394,B_396),k2_relat_1('#skF_6'(A_394,B_396)),C_395),B_396)
      | ~ r2_hidden(C_395,k2_relat_1('#skF_6'(A_394,B_396))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_720])).

tff(c_4226,plain,(
    ! [A_394,C_134,B_4] :
      ( o_1_0_funct_1(A_394) = C_134
      | ~ r1_tarski(k1_relat_1('#skF_6'(A_394,B_4)),B_4)
      | ~ r2_hidden(C_134,k2_relat_1('#skF_6'(A_394,B_4)))
      | ~ v1_funct_1('#skF_6'(A_394,B_4))
      | ~ v1_relat_1('#skF_6'(A_394,B_4)) ) ),
    inference(resolution,[status(thm)],[c_630,c_4219])).

tff(c_4246,plain,(
    ! [A_397,C_398,B_399] :
      ( o_1_0_funct_1(A_397) = C_398
      | ~ r2_hidden(C_398,k2_relat_1('#skF_6'(A_397,B_399))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_299,c_40,c_4226])).

tff(c_17476,plain,(
    ! [A_5024,B_5025,B_5026] :
      ( '#skF_1'(k2_relat_1('#skF_6'(A_5024,B_5025)),B_5026) = o_1_0_funct_1(A_5024)
      | r1_tarski(k2_relat_1('#skF_6'(A_5024,B_5025)),B_5026) ) ),
    inference(resolution,[status(thm)],[c_10,c_4246])).

tff(c_52,plain,(
    ! [C_63] :
      ( ~ r1_tarski(k2_relat_1(C_63),'#skF_7')
      | k1_relat_1(C_63) != '#skF_8'
      | ~ v1_funct_1(C_63)
      | ~ v1_relat_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_17619,plain,(
    ! [A_5024,B_5025] :
      ( k1_relat_1('#skF_6'(A_5024,B_5025)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_5024,B_5025))
      | ~ v1_relat_1('#skF_6'(A_5024,B_5025))
      | '#skF_1'(k2_relat_1('#skF_6'(A_5024,B_5025)),'#skF_7') = o_1_0_funct_1(A_5024) ) ),
    inference(resolution,[status(thm)],[c_17476,c_52])).

tff(c_17745,plain,(
    ! [B_5045,A_5046] :
      ( B_5045 != '#skF_8'
      | '#skF_1'(k2_relat_1('#skF_6'(A_5046,B_5045)),'#skF_7') = o_1_0_funct_1(A_5046) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_17619])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18695,plain,(
    ! [A_5228,B_5229] :
      ( ~ r2_hidden(o_1_0_funct_1(A_5228),'#skF_7')
      | r1_tarski(k2_relat_1('#skF_6'(A_5228,B_5229)),'#skF_7')
      | B_5229 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17745,c_8])).

tff(c_18729,plain,(
    ! [A_5228,B_5229] :
      ( k1_relat_1('#skF_6'(A_5228,B_5229)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_5228,B_5229))
      | ~ v1_relat_1('#skF_6'(A_5228,B_5229))
      | ~ r2_hidden(o_1_0_funct_1(A_5228),'#skF_7')
      | B_5229 != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_18695,c_52])).

tff(c_18798,plain,(
    ! [A_5228,B_5229] :
      ( ~ r2_hidden(o_1_0_funct_1(A_5228),'#skF_7')
      | B_5229 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_18729])).

tff(c_18806,plain,(
    ! [B_5229] : B_5229 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_18798])).

tff(c_18810,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_18806])).

tff(c_18893,plain,(
    ! [A_5267] : ~ r2_hidden(o_1_0_funct_1(A_5267),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_18798])).

tff(c_18898,plain,(
    ! [A_5267] :
      ( v1_xboole_0('#skF_7')
      | ~ m1_subset_1(o_1_0_funct_1(A_5267),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_46,c_18893])).

tff(c_18900,plain,(
    ! [A_5286] : ~ m1_subset_1(o_1_0_funct_1(A_5286),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_18898])).

tff(c_18906,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_32,c_18900])).

tff(c_18907,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_18898])).

tff(c_50,plain,(
    ! [A_61] :
      ( k1_xboole_0 = A_61
      | ~ v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_18916,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_18907,c_50])).

tff(c_18928,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_18916])).

tff(c_18929,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_18950,plain,(
    ! [A_5326] :
      ( A_5326 = '#skF_8'
      | ~ v1_xboole_0(A_5326) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18929,c_50])).

tff(c_18954,plain,(
    o_0_0_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_30,c_18950])).

tff(c_56,plain,(
    ! [A_65] :
      ( v1_relat_1(A_65)
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    v1_relat_1(o_0_0_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_56])).

tff(c_18956,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18954,c_60])).

tff(c_18942,plain,(
    ! [A_5324] :
      ( v1_funct_1(A_5324)
      | ~ v1_xboole_0(A_5324) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_18946,plain,(
    v1_funct_1(o_0_0_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_18942])).

tff(c_18955,plain,(
    v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18954,c_18946])).

tff(c_18957,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18954,c_30])).

tff(c_18992,plain,(
    ! [A_5332] :
      ( v1_xboole_0(k1_relat_1(A_5332))
      | ~ v1_xboole_0(A_5332) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18949,plain,(
    ! [A_61] :
      ( A_61 = '#skF_8'
      | ~ v1_xboole_0(A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18929,c_50])).

tff(c_19025,plain,(
    ! [A_5337] :
      ( k1_relat_1(A_5337) = '#skF_8'
      | ~ v1_xboole_0(A_5337) ) ),
    inference(resolution,[status(thm)],[c_18992,c_18949])).

tff(c_19037,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_18957,c_19025])).

tff(c_48,plain,(
    ! [A_60] : r1_tarski(k1_xboole_0,A_60) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18931,plain,(
    ! [A_60] : r1_tarski('#skF_8',A_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18929,c_48])).

tff(c_18979,plain,(
    ! [A_5331] :
      ( v1_xboole_0(k2_relat_1(A_5331))
      | ~ v1_xboole_0(A_5331) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_19059,plain,(
    ! [A_5341] :
      ( k2_relat_1(A_5341) = '#skF_8'
      | ~ v1_xboole_0(A_5341) ) ),
    inference(resolution,[status(thm)],[c_18979,c_18949])).

tff(c_19071,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_18957,c_19059])).

tff(c_18930,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_18936,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18929,c_18930])).

tff(c_18947,plain,(
    ! [C_63] :
      ( ~ r1_tarski(k2_relat_1(C_63),'#skF_8')
      | k1_relat_1(C_63) != '#skF_8'
      | ~ v1_funct_1(C_63)
      | ~ v1_relat_1(C_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18936,c_52])).

tff(c_19081,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | k1_relat_1('#skF_8') != '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_19071,c_18947])).

tff(c_19090,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18956,c_18955,c_19037,c_18931,c_19081])).

%------------------------------------------------------------------------------
