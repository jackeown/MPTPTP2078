%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:43 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 290 expanded)
%              Number of leaves         :   37 ( 114 expanded)
%              Depth                    :   14
%              Number of atoms          :  196 ( 938 expanded)
%              Number of equality atoms :   44 ( 220 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_107,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_20,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_84,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_87,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_84])).

tff(c_90,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_87])).

tff(c_122,plain,(
    ! [C_64,A_65,B_66] :
      ( v4_relat_1(C_64,A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_126,plain,(
    v4_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_122])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_44,plain,
    ( '#skF_7' != '#skF_8'
    | ~ v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_63,plain,(
    ~ v2_funct_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_42,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_180,plain,(
    ! [A_78] :
      ( r2_hidden('#skF_3'(A_78),k1_relat_1(A_78))
      | v2_funct_1(A_78)
      | ~ v1_funct_1(A_78)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_186,plain,(
    ! [A_78,B_6] :
      ( r2_hidden('#skF_3'(A_78),B_6)
      | ~ r1_tarski(k1_relat_1(A_78),B_6)
      | v2_funct_1(A_78)
      | ~ v1_funct_1(A_78)
      | ~ v1_relat_1(A_78) ) ),
    inference(resolution,[status(thm)],[c_180,c_6])).

tff(c_154,plain,(
    ! [A_73] :
      ( '#skF_4'(A_73) != '#skF_3'(A_73)
      | v2_funct_1(A_73)
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_157,plain,
    ( '#skF_4'('#skF_6') != '#skF_3'('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_154,c_63])).

tff(c_160,plain,(
    '#skF_4'('#skF_6') != '#skF_3'('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_42,c_157])).

tff(c_170,plain,(
    ! [A_76] :
      ( r2_hidden('#skF_4'(A_76),k1_relat_1(A_76))
      | v2_funct_1(A_76)
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_176,plain,(
    ! [A_76,B_6] :
      ( r2_hidden('#skF_4'(A_76),B_6)
      | ~ r1_tarski(k1_relat_1(A_76),B_6)
      | v2_funct_1(A_76)
      | ~ v1_funct_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(resolution,[status(thm)],[c_170,c_6])).

tff(c_230,plain,(
    ! [A_91] :
      ( k1_funct_1(A_91,'#skF_4'(A_91)) = k1_funct_1(A_91,'#skF_3'(A_91))
      | v2_funct_1(A_91)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_62,plain,(
    ! [D_36,C_35] :
      ( v2_funct_1('#skF_6')
      | D_36 = C_35
      | k1_funct_1('#skF_6',D_36) != k1_funct_1('#skF_6',C_35)
      | ~ r2_hidden(D_36,'#skF_5')
      | ~ r2_hidden(C_35,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_127,plain,(
    ! [D_36,C_35] :
      ( D_36 = C_35
      | k1_funct_1('#skF_6',D_36) != k1_funct_1('#skF_6',C_35)
      | ~ r2_hidden(D_36,'#skF_5')
      | ~ r2_hidden(C_35,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_62])).

tff(c_239,plain,(
    ! [D_36] :
      ( D_36 = '#skF_4'('#skF_6')
      | k1_funct_1('#skF_6',D_36) != k1_funct_1('#skF_6','#skF_3'('#skF_6'))
      | ~ r2_hidden(D_36,'#skF_5')
      | ~ r2_hidden('#skF_4'('#skF_6'),'#skF_5')
      | v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_127])).

tff(c_248,plain,(
    ! [D_36] :
      ( D_36 = '#skF_4'('#skF_6')
      | k1_funct_1('#skF_6',D_36) != k1_funct_1('#skF_6','#skF_3'('#skF_6'))
      | ~ r2_hidden(D_36,'#skF_5')
      | ~ r2_hidden('#skF_4'('#skF_6'),'#skF_5')
      | v2_funct_1('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_42,c_239])).

tff(c_249,plain,(
    ! [D_36] :
      ( D_36 = '#skF_4'('#skF_6')
      | k1_funct_1('#skF_6',D_36) != k1_funct_1('#skF_6','#skF_3'('#skF_6'))
      | ~ r2_hidden(D_36,'#skF_5')
      | ~ r2_hidden('#skF_4'('#skF_6'),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_248])).

tff(c_335,plain,(
    ~ r2_hidden('#skF_4'('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_338,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_5')
    | v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_176,c_335])).

tff(c_341,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_5')
    | v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_42,c_338])).

tff(c_342,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_341])).

tff(c_345,plain,
    ( ~ v4_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_342])).

tff(c_352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_126,c_345])).

tff(c_353,plain,(
    ! [D_36] :
      ( D_36 = '#skF_4'('#skF_6')
      | k1_funct_1('#skF_6',D_36) != k1_funct_1('#skF_6','#skF_3'('#skF_6'))
      | ~ r2_hidden(D_36,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_415,plain,
    ( '#skF_4'('#skF_6') = '#skF_3'('#skF_6')
    | ~ r2_hidden('#skF_3'('#skF_6'),'#skF_5') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_353])).

tff(c_416,plain,(
    ~ r2_hidden('#skF_3'('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_415])).

tff(c_428,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_5')
    | v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_186,c_416])).

tff(c_431,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_5')
    | v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_42,c_428])).

tff(c_432,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_431])).

tff(c_435,plain,
    ( ~ v4_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_432])).

tff(c_442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_126,c_435])).

tff(c_444,plain,(
    v2_funct_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_48,plain,
    ( r2_hidden('#skF_8','#skF_5')
    | ~ v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_447,plain,(
    r2_hidden('#skF_8','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_48])).

tff(c_448,plain,(
    ! [B_122,A_123] :
      ( ~ r2_hidden(B_122,A_123)
      | ~ v1_xboole_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_452,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_447,c_448])).

tff(c_40,plain,(
    v1_funct_2('#skF_6','#skF_5','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_46,plain,
    ( k1_funct_1('#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_8')
    | ~ v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_485,plain,(
    k1_funct_1('#skF_6','#skF_7') = k1_funct_1('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_46])).

tff(c_50,plain,
    ( r2_hidden('#skF_7','#skF_5')
    | ~ v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_454,plain,(
    r2_hidden('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_50])).

tff(c_800,plain,(
    ! [D_207,C_208,B_209,A_210] :
      ( k1_funct_1(k2_funct_1(D_207),k1_funct_1(D_207,C_208)) = C_208
      | k1_xboole_0 = B_209
      | ~ r2_hidden(C_208,A_210)
      | ~ v2_funct_1(D_207)
      | ~ m1_subset_1(D_207,k1_zfmisc_1(k2_zfmisc_1(A_210,B_209)))
      | ~ v1_funct_2(D_207,A_210,B_209)
      | ~ v1_funct_1(D_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_873,plain,(
    ! [D_221,B_222] :
      ( k1_funct_1(k2_funct_1(D_221),k1_funct_1(D_221,'#skF_7')) = '#skF_7'
      | k1_xboole_0 = B_222
      | ~ v2_funct_1(D_221)
      | ~ m1_subset_1(D_221,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_222)))
      | ~ v1_funct_2(D_221,'#skF_5',B_222)
      | ~ v1_funct_1(D_221) ) ),
    inference(resolution,[status(thm)],[c_454,c_800])).

tff(c_875,plain,
    ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_873])).

tff(c_878,plain,
    ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_8')) = '#skF_7'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_444,c_485,c_875])).

tff(c_879,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_878])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_882,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_879,c_12])).

tff(c_884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_452,c_882])).

tff(c_886,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_878])).

tff(c_443,plain,(
    '#skF_7' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_885,plain,(
    k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_8')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_878])).

tff(c_911,plain,(
    ! [D_226,B_227] :
      ( k1_funct_1(k2_funct_1(D_226),k1_funct_1(D_226,'#skF_8')) = '#skF_8'
      | k1_xboole_0 = B_227
      | ~ v2_funct_1(D_226)
      | ~ m1_subset_1(D_226,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_227)))
      | ~ v1_funct_2(D_226,'#skF_5',B_227)
      | ~ v1_funct_1(D_226) ) ),
    inference(resolution,[status(thm)],[c_447,c_800])).

tff(c_913,plain,
    ( k1_funct_1(k2_funct_1('#skF_6'),k1_funct_1('#skF_6','#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_911])).

tff(c_916,plain,
    ( '#skF_7' = '#skF_8'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_444,c_885,c_913])).

tff(c_918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_886,c_443,c_916])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:11:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.48  
% 3.13/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.48  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2
% 3.33/1.48  
% 3.33/1.48  %Foreground sorts:
% 3.33/1.48  
% 3.33/1.48  
% 3.33/1.48  %Background operators:
% 3.33/1.48  
% 3.33/1.48  
% 3.33/1.48  %Foreground operators:
% 3.33/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.33/1.48  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.33/1.48  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.33/1.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.33/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.33/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.33/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.33/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.33/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.33/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.33/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.33/1.48  tff('#skF_8', type, '#skF_8': $i).
% 3.33/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.33/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.33/1.48  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.33/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.33/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.33/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.33/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.33/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.48  
% 3.33/1.50  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.33/1.50  tff(f_107, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 3.33/1.50  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.33/1.50  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.33/1.50  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.33/1.50  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 3.33/1.50  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.33/1.50  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.33/1.50  tff(f_89, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 3.33/1.50  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.33/1.50  tff(c_20, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.33/1.50  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.33/1.50  tff(c_84, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.33/1.50  tff(c_87, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_5'))), inference(resolution, [status(thm)], [c_38, c_84])).
% 3.33/1.50  tff(c_90, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_87])).
% 3.33/1.50  tff(c_122, plain, (![C_64, A_65, B_66]: (v4_relat_1(C_64, A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.33/1.50  tff(c_126, plain, (v4_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_38, c_122])).
% 3.33/1.50  tff(c_18, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(B_14), A_13) | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.33/1.50  tff(c_44, plain, ('#skF_7'!='#skF_8' | ~v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.33/1.50  tff(c_63, plain, (~v2_funct_1('#skF_6')), inference(splitLeft, [status(thm)], [c_44])).
% 3.33/1.50  tff(c_42, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.33/1.50  tff(c_180, plain, (![A_78]: (r2_hidden('#skF_3'(A_78), k1_relat_1(A_78)) | v2_funct_1(A_78) | ~v1_funct_1(A_78) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.33/1.50  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.33/1.50  tff(c_186, plain, (![A_78, B_6]: (r2_hidden('#skF_3'(A_78), B_6) | ~r1_tarski(k1_relat_1(A_78), B_6) | v2_funct_1(A_78) | ~v1_funct_1(A_78) | ~v1_relat_1(A_78))), inference(resolution, [status(thm)], [c_180, c_6])).
% 3.33/1.50  tff(c_154, plain, (![A_73]: ('#skF_4'(A_73)!='#skF_3'(A_73) | v2_funct_1(A_73) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.33/1.50  tff(c_157, plain, ('#skF_4'('#skF_6')!='#skF_3'('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_154, c_63])).
% 3.33/1.50  tff(c_160, plain, ('#skF_4'('#skF_6')!='#skF_3'('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_42, c_157])).
% 3.33/1.50  tff(c_170, plain, (![A_76]: (r2_hidden('#skF_4'(A_76), k1_relat_1(A_76)) | v2_funct_1(A_76) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.33/1.50  tff(c_176, plain, (![A_76, B_6]: (r2_hidden('#skF_4'(A_76), B_6) | ~r1_tarski(k1_relat_1(A_76), B_6) | v2_funct_1(A_76) | ~v1_funct_1(A_76) | ~v1_relat_1(A_76))), inference(resolution, [status(thm)], [c_170, c_6])).
% 3.33/1.50  tff(c_230, plain, (![A_91]: (k1_funct_1(A_91, '#skF_4'(A_91))=k1_funct_1(A_91, '#skF_3'(A_91)) | v2_funct_1(A_91) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.33/1.50  tff(c_62, plain, (![D_36, C_35]: (v2_funct_1('#skF_6') | D_36=C_35 | k1_funct_1('#skF_6', D_36)!=k1_funct_1('#skF_6', C_35) | ~r2_hidden(D_36, '#skF_5') | ~r2_hidden(C_35, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.33/1.50  tff(c_127, plain, (![D_36, C_35]: (D_36=C_35 | k1_funct_1('#skF_6', D_36)!=k1_funct_1('#skF_6', C_35) | ~r2_hidden(D_36, '#skF_5') | ~r2_hidden(C_35, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_63, c_62])).
% 3.33/1.50  tff(c_239, plain, (![D_36]: (D_36='#skF_4'('#skF_6') | k1_funct_1('#skF_6', D_36)!=k1_funct_1('#skF_6', '#skF_3'('#skF_6')) | ~r2_hidden(D_36, '#skF_5') | ~r2_hidden('#skF_4'('#skF_6'), '#skF_5') | v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_230, c_127])).
% 3.33/1.50  tff(c_248, plain, (![D_36]: (D_36='#skF_4'('#skF_6') | k1_funct_1('#skF_6', D_36)!=k1_funct_1('#skF_6', '#skF_3'('#skF_6')) | ~r2_hidden(D_36, '#skF_5') | ~r2_hidden('#skF_4'('#skF_6'), '#skF_5') | v2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_42, c_239])).
% 3.33/1.50  tff(c_249, plain, (![D_36]: (D_36='#skF_4'('#skF_6') | k1_funct_1('#skF_6', D_36)!=k1_funct_1('#skF_6', '#skF_3'('#skF_6')) | ~r2_hidden(D_36, '#skF_5') | ~r2_hidden('#skF_4'('#skF_6'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_63, c_248])).
% 3.33/1.50  tff(c_335, plain, (~r2_hidden('#skF_4'('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_249])).
% 3.33/1.50  tff(c_338, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_5') | v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_176, c_335])).
% 3.33/1.50  tff(c_341, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_5') | v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_42, c_338])).
% 3.33/1.50  tff(c_342, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_63, c_341])).
% 3.33/1.50  tff(c_345, plain, (~v4_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_18, c_342])).
% 3.33/1.50  tff(c_352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_126, c_345])).
% 3.33/1.50  tff(c_353, plain, (![D_36]: (D_36='#skF_4'('#skF_6') | k1_funct_1('#skF_6', D_36)!=k1_funct_1('#skF_6', '#skF_3'('#skF_6')) | ~r2_hidden(D_36, '#skF_5'))), inference(splitRight, [status(thm)], [c_249])).
% 3.33/1.50  tff(c_415, plain, ('#skF_4'('#skF_6')='#skF_3'('#skF_6') | ~r2_hidden('#skF_3'('#skF_6'), '#skF_5')), inference(reflexivity, [status(thm), theory('equality')], [c_353])).
% 3.33/1.50  tff(c_416, plain, (~r2_hidden('#skF_3'('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_160, c_415])).
% 3.33/1.50  tff(c_428, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_5') | v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_186, c_416])).
% 3.33/1.50  tff(c_431, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_5') | v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_42, c_428])).
% 3.33/1.50  tff(c_432, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_63, c_431])).
% 3.33/1.50  tff(c_435, plain, (~v4_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_18, c_432])).
% 3.33/1.50  tff(c_442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_126, c_435])).
% 3.33/1.50  tff(c_444, plain, (v2_funct_1('#skF_6')), inference(splitRight, [status(thm)], [c_44])).
% 3.33/1.50  tff(c_48, plain, (r2_hidden('#skF_8', '#skF_5') | ~v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.33/1.50  tff(c_447, plain, (r2_hidden('#skF_8', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_444, c_48])).
% 3.33/1.50  tff(c_448, plain, (![B_122, A_123]: (~r2_hidden(B_122, A_123) | ~v1_xboole_0(A_123))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.33/1.50  tff(c_452, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_447, c_448])).
% 3.33/1.50  tff(c_40, plain, (v1_funct_2('#skF_6', '#skF_5', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.33/1.50  tff(c_46, plain, (k1_funct_1('#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_8') | ~v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.33/1.50  tff(c_485, plain, (k1_funct_1('#skF_6', '#skF_7')=k1_funct_1('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_444, c_46])).
% 3.33/1.50  tff(c_50, plain, (r2_hidden('#skF_7', '#skF_5') | ~v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.33/1.50  tff(c_454, plain, (r2_hidden('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_444, c_50])).
% 3.33/1.50  tff(c_800, plain, (![D_207, C_208, B_209, A_210]: (k1_funct_1(k2_funct_1(D_207), k1_funct_1(D_207, C_208))=C_208 | k1_xboole_0=B_209 | ~r2_hidden(C_208, A_210) | ~v2_funct_1(D_207) | ~m1_subset_1(D_207, k1_zfmisc_1(k2_zfmisc_1(A_210, B_209))) | ~v1_funct_2(D_207, A_210, B_209) | ~v1_funct_1(D_207))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.33/1.50  tff(c_873, plain, (![D_221, B_222]: (k1_funct_1(k2_funct_1(D_221), k1_funct_1(D_221, '#skF_7'))='#skF_7' | k1_xboole_0=B_222 | ~v2_funct_1(D_221) | ~m1_subset_1(D_221, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_222))) | ~v1_funct_2(D_221, '#skF_5', B_222) | ~v1_funct_1(D_221))), inference(resolution, [status(thm)], [c_454, c_800])).
% 3.33/1.50  tff(c_875, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_7'))='#skF_7' | k1_xboole_0='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_873])).
% 3.33/1.50  tff(c_878, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_8'))='#skF_7' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_444, c_485, c_875])).
% 3.33/1.50  tff(c_879, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_878])).
% 3.33/1.50  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.33/1.50  tff(c_882, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_879, c_12])).
% 3.33/1.50  tff(c_884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_452, c_882])).
% 3.33/1.50  tff(c_886, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_878])).
% 3.33/1.50  tff(c_443, plain, ('#skF_7'!='#skF_8'), inference(splitRight, [status(thm)], [c_44])).
% 3.33/1.50  tff(c_885, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_8'))='#skF_7'), inference(splitRight, [status(thm)], [c_878])).
% 3.33/1.50  tff(c_911, plain, (![D_226, B_227]: (k1_funct_1(k2_funct_1(D_226), k1_funct_1(D_226, '#skF_8'))='#skF_8' | k1_xboole_0=B_227 | ~v2_funct_1(D_226) | ~m1_subset_1(D_226, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_227))) | ~v1_funct_2(D_226, '#skF_5', B_227) | ~v1_funct_1(D_226))), inference(resolution, [status(thm)], [c_447, c_800])).
% 3.33/1.50  tff(c_913, plain, (k1_funct_1(k2_funct_1('#skF_6'), k1_funct_1('#skF_6', '#skF_8'))='#skF_8' | k1_xboole_0='#skF_5' | ~v2_funct_1('#skF_6') | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_911])).
% 3.33/1.50  tff(c_916, plain, ('#skF_7'='#skF_8' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_444, c_885, c_913])).
% 3.33/1.50  tff(c_918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_886, c_443, c_916])).
% 3.33/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.50  
% 3.33/1.50  Inference rules
% 3.33/1.50  ----------------------
% 3.33/1.50  #Ref     : 4
% 3.33/1.50  #Sup     : 191
% 3.33/1.50  #Fact    : 0
% 3.33/1.50  #Define  : 0
% 3.33/1.50  #Split   : 7
% 3.33/1.50  #Chain   : 0
% 3.33/1.50  #Close   : 0
% 3.33/1.50  
% 3.33/1.50  Ordering : KBO
% 3.33/1.50  
% 3.33/1.50  Simplification rules
% 3.33/1.50  ----------------------
% 3.33/1.50  #Subsume      : 68
% 3.33/1.50  #Demod        : 54
% 3.33/1.50  #Tautology    : 36
% 3.33/1.50  #SimpNegUnit  : 10
% 3.33/1.50  #BackRed      : 3
% 3.33/1.50  
% 3.33/1.50  #Partial instantiations: 0
% 3.33/1.50  #Strategies tried      : 1
% 3.33/1.50  
% 3.33/1.50  Timing (in seconds)
% 3.33/1.50  ----------------------
% 3.33/1.50  Preprocessing        : 0.32
% 3.33/1.51  Parsing              : 0.16
% 3.33/1.51  CNF conversion       : 0.02
% 3.33/1.51  Main loop            : 0.41
% 3.33/1.51  Inferencing          : 0.16
% 3.33/1.51  Reduction            : 0.11
% 3.33/1.51  Demodulation         : 0.07
% 3.33/1.51  BG Simplification    : 0.02
% 3.33/1.51  Subsumption          : 0.09
% 3.33/1.51  Abstraction          : 0.02
% 3.33/1.51  MUC search           : 0.00
% 3.33/1.51  Cooper               : 0.00
% 3.33/1.51  Total                : 0.76
% 3.33/1.51  Index Insertion      : 0.00
% 3.33/1.51  Index Deletion       : 0.00
% 3.33/1.51  Index Matching       : 0.00
% 3.33/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
