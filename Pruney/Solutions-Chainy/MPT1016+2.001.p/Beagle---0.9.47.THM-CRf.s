%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:40 EST 2020

% Result     : Theorem 4.42s
% Output     : CNFRefutation 4.42s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 680 expanded)
%              Number of leaves         :   37 ( 243 expanded)
%              Depth                    :   17
%              Number of atoms          :  293 (1862 expanded)
%              Number of equality atoms :   58 ( 287 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_113,negated_conjecture,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_71,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_46,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_82,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_91,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_82])).

tff(c_158,plain,(
    ! [C_67,A_68,B_69] :
      ( v4_relat_1(C_67,A_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_167,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_158])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,
    ( '#skF_7' != '#skF_6'
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_71,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_316,plain,(
    ! [A_110] :
      ( r2_hidden('#skF_3'(A_110),k1_relat_1(A_110))
      | v2_funct_1(A_110)
      | ~ v1_funct_1(A_110)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2220,plain,(
    ! [A_267,B_268] :
      ( r2_hidden('#skF_3'(A_267),B_268)
      | ~ r1_tarski(k1_relat_1(A_267),B_268)
      | v2_funct_1(A_267)
      | ~ v1_funct_1(A_267)
      | ~ v1_relat_1(A_267) ) ),
    inference(resolution,[status(thm)],[c_316,c_2])).

tff(c_262,plain,(
    ! [A_99] :
      ( '#skF_2'(A_99) != '#skF_3'(A_99)
      | v2_funct_1(A_99)
      | ~ v1_funct_1(A_99)
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_265,plain,
    ( '#skF_2'('#skF_5') != '#skF_3'('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_262,c_71])).

tff(c_268,plain,(
    '#skF_2'('#skF_5') != '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_48,c_265])).

tff(c_407,plain,(
    ! [A_124] :
      ( r2_hidden('#skF_2'(A_124),k1_relat_1(A_124))
      | v2_funct_1(A_124)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1081,plain,(
    ! [A_179,B_180] :
      ( r2_hidden('#skF_2'(A_179),B_180)
      | ~ r1_tarski(k1_relat_1(A_179),B_180)
      | v2_funct_1(A_179)
      | ~ v1_funct_1(A_179)
      | ~ v1_relat_1(A_179) ) ),
    inference(resolution,[status(thm)],[c_407,c_2])).

tff(c_468,plain,(
    ! [A_128] :
      ( k1_funct_1(A_128,'#skF_2'(A_128)) = k1_funct_1(A_128,'#skF_3'(A_128))
      | v2_funct_1(A_128)
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_68,plain,(
    ! [D_37,C_36] :
      ( v2_funct_1('#skF_5')
      | D_37 = C_36
      | k1_funct_1('#skF_5',D_37) != k1_funct_1('#skF_5',C_36)
      | ~ r2_hidden(D_37,'#skF_4')
      | ~ r2_hidden(C_36,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_115,plain,(
    ! [D_37,C_36] :
      ( D_37 = C_36
      | k1_funct_1('#skF_5',D_37) != k1_funct_1('#skF_5',C_36)
      | ~ r2_hidden(D_37,'#skF_4')
      | ~ r2_hidden(C_36,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_68])).

tff(c_477,plain,(
    ! [D_37] :
      ( D_37 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_37) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_37,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_115])).

tff(c_486,plain,(
    ! [D_37] :
      ( D_37 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_37) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_37,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_48,c_477])).

tff(c_487,plain,(
    ! [D_37] :
      ( D_37 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_37) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_37,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_486])).

tff(c_571,plain,(
    ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_487])).

tff(c_1086,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1081,c_571])).

tff(c_1094,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_48,c_1086])).

tff(c_1095,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_1094])).

tff(c_1106,plain,
    ( ~ v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_1095])).

tff(c_1114,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_167,c_1106])).

tff(c_1116,plain,(
    r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_487])).

tff(c_474,plain,(
    ! [C_36] :
      ( C_36 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_36) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_36,'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_115])).

tff(c_483,plain,(
    ! [C_36] :
      ( C_36 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_36) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_36,'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_48,c_474])).

tff(c_484,plain,(
    ! [C_36] :
      ( C_36 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_36) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_36,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_483])).

tff(c_1135,plain,(
    ! [C_36] :
      ( C_36 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_36) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(C_36,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1116,c_484])).

tff(c_1138,plain,
    ( '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1135])).

tff(c_1139,plain,(
    ~ r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_268,c_1138])).

tff(c_2225,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2220,c_1139])).

tff(c_2233,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_48,c_2225])).

tff(c_2234,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_2233])).

tff(c_2245,plain,
    ( ~ v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_2234])).

tff(c_2253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_167,c_2245])).

tff(c_2255,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_56,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2259,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2255,c_56])).

tff(c_3231,plain,(
    ! [D_400,C_401,B_402,A_403] :
      ( k1_funct_1(k2_funct_1(D_400),k1_funct_1(D_400,C_401)) = C_401
      | k1_xboole_0 = B_402
      | ~ r2_hidden(C_401,A_403)
      | ~ v2_funct_1(D_400)
      | ~ m1_subset_1(D_400,k1_zfmisc_1(k2_zfmisc_1(A_403,B_402)))
      | ~ v1_funct_2(D_400,A_403,B_402)
      | ~ v1_funct_1(D_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3358,plain,(
    ! [D_409,B_410] :
      ( k1_funct_1(k2_funct_1(D_409),k1_funct_1(D_409,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_410
      | ~ v2_funct_1(D_409)
      | ~ m1_subset_1(D_409,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_410)))
      | ~ v1_funct_2(D_409,'#skF_4',B_410)
      | ~ v1_funct_1(D_409) ) ),
    inference(resolution,[status(thm)],[c_2259,c_3231])).

tff(c_3363,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_3358])).

tff(c_3367,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_2255,c_3363])).

tff(c_3368,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3367])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2352,plain,(
    ! [C_297,B_298,A_299] :
      ( ~ v1_xboole_0(C_297)
      | ~ m1_subset_1(B_298,k1_zfmisc_1(C_297))
      | ~ r2_hidden(A_299,B_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2360,plain,(
    ! [B_300,A_301,A_302] :
      ( ~ v1_xboole_0(B_300)
      | ~ r2_hidden(A_301,A_302)
      | ~ r1_tarski(A_302,B_300) ) ),
    inference(resolution,[status(thm)],[c_18,c_2352])).

tff(c_2411,plain,(
    ! [B_311,A_312,B_313] :
      ( ~ v1_xboole_0(B_311)
      | ~ r1_tarski(A_312,B_311)
      | r1_tarski(A_312,B_313) ) ),
    inference(resolution,[status(thm)],[c_6,c_2360])).

tff(c_2421,plain,(
    ! [B_314,B_315] :
      ( ~ v1_xboole_0(B_314)
      | r1_tarski(B_314,B_315) ) ),
    inference(resolution,[status(thm)],[c_14,c_2411])).

tff(c_2281,plain,(
    ! [C_277,A_278,B_279] :
      ( v1_relat_1(C_277)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(A_278,B_279))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2289,plain,(
    ! [A_8,A_278,B_279] :
      ( v1_relat_1(A_8)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_278,B_279)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2281])).

tff(c_2446,plain,(
    ! [B_316] :
      ( v1_relat_1(B_316)
      | ~ v1_xboole_0(B_316) ) ),
    inference(resolution,[status(thm)],[c_2421,c_2289])).

tff(c_2450,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_2446])).

tff(c_2316,plain,(
    ! [C_287,A_288,B_289] :
      ( v4_relat_1(C_287,A_288)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_288,B_289))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2324,plain,(
    ! [A_8,A_288,B_289] :
      ( v4_relat_1(A_8,A_288)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_288,B_289)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2316])).

tff(c_2443,plain,(
    ! [B_314,A_288] :
      ( v4_relat_1(B_314,A_288)
      | ~ v1_xboole_0(B_314) ) ),
    inference(resolution,[status(thm)],[c_2421,c_2324])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2469,plain,(
    ! [B_323,B_322] :
      ( B_323 = B_322
      | ~ r1_tarski(B_322,B_323)
      | ~ v1_xboole_0(B_323) ) ),
    inference(resolution,[status(thm)],[c_2421,c_10])).

tff(c_2585,plain,(
    ! [B_351,A_352] :
      ( k1_relat_1(B_351) = A_352
      | ~ v1_xboole_0(A_352)
      | ~ v4_relat_1(B_351,A_352)
      | ~ v1_relat_1(B_351) ) ),
    inference(resolution,[status(thm)],[c_24,c_2469])).

tff(c_2673,plain,(
    ! [B_361,A_362] :
      ( k1_relat_1(B_361) = A_362
      | ~ v1_xboole_0(A_362)
      | ~ v1_relat_1(B_361)
      | ~ v1_xboole_0(B_361) ) ),
    inference(resolution,[status(thm)],[c_2443,c_2585])).

tff(c_2677,plain,(
    ! [B_363] :
      ( k1_relat_1(B_363) = k1_xboole_0
      | ~ v1_relat_1(B_363)
      | ~ v1_xboole_0(B_363) ) ),
    inference(resolution,[status(thm)],[c_8,c_2673])).

tff(c_2680,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_2677])).

tff(c_2683,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2450,c_2680])).

tff(c_2420,plain,(
    ! [B_7,B_313] :
      ( ~ v1_xboole_0(B_7)
      | r1_tarski(B_7,B_313) ) ),
    inference(resolution,[status(thm)],[c_14,c_2411])).

tff(c_2451,plain,(
    ! [B_317,A_318] :
      ( v4_relat_1(B_317,A_318)
      | ~ r1_tarski(k1_relat_1(B_317),A_318)
      | ~ v1_relat_1(B_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2463,plain,(
    ! [B_317,B_313] :
      ( v4_relat_1(B_317,B_313)
      | ~ v1_relat_1(B_317)
      | ~ v1_xboole_0(k1_relat_1(B_317)) ) ),
    inference(resolution,[status(thm)],[c_2420,c_2451])).

tff(c_2703,plain,(
    ! [B_313] :
      ( v4_relat_1(k1_xboole_0,B_313)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2683,c_2463])).

tff(c_2722,plain,(
    ! [B_313] : v4_relat_1(k1_xboole_0,B_313) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2450,c_2703])).

tff(c_2712,plain,(
    ! [A_13] :
      ( r1_tarski(k1_xboole_0,A_13)
      | ~ v4_relat_1(k1_xboole_0,A_13)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2683,c_24])).

tff(c_2728,plain,(
    ! [A_13] :
      ( r1_tarski(k1_xboole_0,A_13)
      | ~ v4_relat_1(k1_xboole_0,A_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2450,c_2712])).

tff(c_2748,plain,(
    ! [A_367] : r1_tarski(k1_xboole_0,A_367) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2722,c_2728])).

tff(c_2376,plain,(
    ! [C_304,B_305,A_306] :
      ( r2_hidden(C_304,B_305)
      | ~ r2_hidden(C_304,A_306)
      | ~ r1_tarski(A_306,B_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2386,plain,(
    ! [B_307] :
      ( r2_hidden('#skF_6',B_307)
      | ~ r1_tarski('#skF_4',B_307) ) ),
    inference(resolution,[status(thm)],[c_2259,c_2376])).

tff(c_2357,plain,(
    ! [B_9,A_299,A_8] :
      ( ~ v1_xboole_0(B_9)
      | ~ r2_hidden(A_299,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_2352])).

tff(c_2392,plain,(
    ! [B_9,B_307] :
      ( ~ v1_xboole_0(B_9)
      | ~ r1_tarski(B_307,B_9)
      | ~ r1_tarski('#skF_4',B_307) ) ),
    inference(resolution,[status(thm)],[c_2386,c_2357])).

tff(c_2780,plain,(
    ! [A_367] :
      ( ~ v1_xboole_0(A_367)
      | ~ r1_tarski('#skF_4',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2748,c_2392])).

tff(c_2827,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2780])).

tff(c_3378,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3368,c_2827])).

tff(c_3390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_3378])).

tff(c_3392,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3367])).

tff(c_2254,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3391,plain,(
    k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3367])).

tff(c_52,plain,
    ( k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2292,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2255,c_52])).

tff(c_54,plain,
    ( r2_hidden('#skF_7','#skF_4')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2257,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2255,c_54])).

tff(c_3599,plain,(
    ! [D_427,B_428] :
      ( k1_funct_1(k2_funct_1(D_427),k1_funct_1(D_427,'#skF_7')) = '#skF_7'
      | k1_xboole_0 = B_428
      | ~ v2_funct_1(D_427)
      | ~ m1_subset_1(D_427,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_428)))
      | ~ v1_funct_2(D_427,'#skF_4',B_428)
      | ~ v1_funct_1(D_427) ) ),
    inference(resolution,[status(thm)],[c_2257,c_3231])).

tff(c_3604,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_3599])).

tff(c_3608,plain,
    ( '#skF_7' = '#skF_6'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_2255,c_3391,c_2292,c_3604])).

tff(c_3610,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3392,c_2254,c_3608])).

tff(c_3611,plain,(
    ! [A_367] : ~ v1_xboole_0(A_367) ),
    inference(splitRight,[status(thm)],[c_2780])).

tff(c_3614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3611,c_8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:16:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.42/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.90  
% 4.42/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.91  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 4.42/1.91  
% 4.42/1.91  %Foreground sorts:
% 4.42/1.91  
% 4.42/1.91  
% 4.42/1.91  %Background operators:
% 4.42/1.91  
% 4.42/1.91  
% 4.42/1.91  %Foreground operators:
% 4.42/1.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.42/1.91  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.42/1.91  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.42/1.91  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.42/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.42/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.42/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.42/1.91  tff('#skF_7', type, '#skF_7': $i).
% 4.42/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.42/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.42/1.91  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.42/1.91  tff('#skF_6', type, '#skF_6': $i).
% 4.42/1.91  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.42/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.42/1.91  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.42/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.42/1.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.42/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.42/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.42/1.91  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.42/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.42/1.91  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.42/1.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.42/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.42/1.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.42/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.42/1.91  
% 4.42/1.93  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.42/1.93  tff(f_113, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 4.42/1.93  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.42/1.93  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.42/1.93  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.42/1.93  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 4.42/1.93  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.42/1.93  tff(f_95, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 4.42/1.93  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.42/1.93  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.42/1.93  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.42/1.93  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.42/1.93  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.42/1.93  tff(c_46, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.42/1.93  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.42/1.93  tff(c_82, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.42/1.93  tff(c_91, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_82])).
% 4.42/1.93  tff(c_158, plain, (![C_67, A_68, B_69]: (v4_relat_1(C_67, A_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.42/1.93  tff(c_167, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_158])).
% 4.42/1.93  tff(c_24, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(B_14), A_13) | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.42/1.93  tff(c_50, plain, ('#skF_7'!='#skF_6' | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.42/1.93  tff(c_71, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_50])).
% 4.42/1.93  tff(c_316, plain, (![A_110]: (r2_hidden('#skF_3'(A_110), k1_relat_1(A_110)) | v2_funct_1(A_110) | ~v1_funct_1(A_110) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.42/1.93  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.42/1.93  tff(c_2220, plain, (![A_267, B_268]: (r2_hidden('#skF_3'(A_267), B_268) | ~r1_tarski(k1_relat_1(A_267), B_268) | v2_funct_1(A_267) | ~v1_funct_1(A_267) | ~v1_relat_1(A_267))), inference(resolution, [status(thm)], [c_316, c_2])).
% 4.42/1.93  tff(c_262, plain, (![A_99]: ('#skF_2'(A_99)!='#skF_3'(A_99) | v2_funct_1(A_99) | ~v1_funct_1(A_99) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.42/1.93  tff(c_265, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_262, c_71])).
% 4.42/1.93  tff(c_268, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_48, c_265])).
% 4.42/1.93  tff(c_407, plain, (![A_124]: (r2_hidden('#skF_2'(A_124), k1_relat_1(A_124)) | v2_funct_1(A_124) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.42/1.93  tff(c_1081, plain, (![A_179, B_180]: (r2_hidden('#skF_2'(A_179), B_180) | ~r1_tarski(k1_relat_1(A_179), B_180) | v2_funct_1(A_179) | ~v1_funct_1(A_179) | ~v1_relat_1(A_179))), inference(resolution, [status(thm)], [c_407, c_2])).
% 4.42/1.93  tff(c_468, plain, (![A_128]: (k1_funct_1(A_128, '#skF_2'(A_128))=k1_funct_1(A_128, '#skF_3'(A_128)) | v2_funct_1(A_128) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.42/1.93  tff(c_68, plain, (![D_37, C_36]: (v2_funct_1('#skF_5') | D_37=C_36 | k1_funct_1('#skF_5', D_37)!=k1_funct_1('#skF_5', C_36) | ~r2_hidden(D_37, '#skF_4') | ~r2_hidden(C_36, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.42/1.93  tff(c_115, plain, (![D_37, C_36]: (D_37=C_36 | k1_funct_1('#skF_5', D_37)!=k1_funct_1('#skF_5', C_36) | ~r2_hidden(D_37, '#skF_4') | ~r2_hidden(C_36, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_71, c_68])).
% 4.42/1.93  tff(c_477, plain, (![D_37]: (D_37='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_37)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_37, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_468, c_115])).
% 4.42/1.93  tff(c_486, plain, (![D_37]: (D_37='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_37)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_37, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_48, c_477])).
% 4.42/1.93  tff(c_487, plain, (![D_37]: (D_37='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_37)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_37, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_71, c_486])).
% 4.42/1.93  tff(c_571, plain, (~r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_487])).
% 4.42/1.93  tff(c_1086, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1081, c_571])).
% 4.42/1.93  tff(c_1094, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_48, c_1086])).
% 4.42/1.93  tff(c_1095, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_71, c_1094])).
% 4.42/1.93  tff(c_1106, plain, (~v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_1095])).
% 4.42/1.93  tff(c_1114, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_167, c_1106])).
% 4.42/1.93  tff(c_1116, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_487])).
% 4.42/1.93  tff(c_474, plain, (![C_36]: (C_36='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_36)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_36, '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_468, c_115])).
% 4.42/1.93  tff(c_483, plain, (![C_36]: (C_36='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_36)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_36, '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_48, c_474])).
% 4.42/1.93  tff(c_484, plain, (![C_36]: (C_36='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_36)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_36, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_71, c_483])).
% 4.42/1.93  tff(c_1135, plain, (![C_36]: (C_36='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_36)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(C_36, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1116, c_484])).
% 4.42/1.93  tff(c_1138, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_1135])).
% 4.42/1.93  tff(c_1139, plain, (~r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_268, c_1138])).
% 4.42/1.93  tff(c_2225, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2220, c_1139])).
% 4.42/1.93  tff(c_2233, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_48, c_2225])).
% 4.42/1.93  tff(c_2234, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_71, c_2233])).
% 4.42/1.93  tff(c_2245, plain, (~v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_24, c_2234])).
% 4.42/1.93  tff(c_2253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_167, c_2245])).
% 4.42/1.93  tff(c_2255, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_50])).
% 4.42/1.93  tff(c_56, plain, (r2_hidden('#skF_6', '#skF_4') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.42/1.93  tff(c_2259, plain, (r2_hidden('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2255, c_56])).
% 4.42/1.93  tff(c_3231, plain, (![D_400, C_401, B_402, A_403]: (k1_funct_1(k2_funct_1(D_400), k1_funct_1(D_400, C_401))=C_401 | k1_xboole_0=B_402 | ~r2_hidden(C_401, A_403) | ~v2_funct_1(D_400) | ~m1_subset_1(D_400, k1_zfmisc_1(k2_zfmisc_1(A_403, B_402))) | ~v1_funct_2(D_400, A_403, B_402) | ~v1_funct_1(D_400))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.42/1.93  tff(c_3358, plain, (![D_409, B_410]: (k1_funct_1(k2_funct_1(D_409), k1_funct_1(D_409, '#skF_6'))='#skF_6' | k1_xboole_0=B_410 | ~v2_funct_1(D_409) | ~m1_subset_1(D_409, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_410))) | ~v1_funct_2(D_409, '#skF_4', B_410) | ~v1_funct_1(D_409))), inference(resolution, [status(thm)], [c_2259, c_3231])).
% 4.42/1.93  tff(c_3363, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_3358])).
% 4.42/1.93  tff(c_3367, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_2255, c_3363])).
% 4.42/1.93  tff(c_3368, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_3367])).
% 4.42/1.93  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.42/1.93  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.42/1.93  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.42/1.93  tff(c_2352, plain, (![C_297, B_298, A_299]: (~v1_xboole_0(C_297) | ~m1_subset_1(B_298, k1_zfmisc_1(C_297)) | ~r2_hidden(A_299, B_298))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.42/1.93  tff(c_2360, plain, (![B_300, A_301, A_302]: (~v1_xboole_0(B_300) | ~r2_hidden(A_301, A_302) | ~r1_tarski(A_302, B_300))), inference(resolution, [status(thm)], [c_18, c_2352])).
% 4.42/1.93  tff(c_2411, plain, (![B_311, A_312, B_313]: (~v1_xboole_0(B_311) | ~r1_tarski(A_312, B_311) | r1_tarski(A_312, B_313))), inference(resolution, [status(thm)], [c_6, c_2360])).
% 4.42/1.93  tff(c_2421, plain, (![B_314, B_315]: (~v1_xboole_0(B_314) | r1_tarski(B_314, B_315))), inference(resolution, [status(thm)], [c_14, c_2411])).
% 4.42/1.93  tff(c_2281, plain, (![C_277, A_278, B_279]: (v1_relat_1(C_277) | ~m1_subset_1(C_277, k1_zfmisc_1(k2_zfmisc_1(A_278, B_279))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.42/1.93  tff(c_2289, plain, (![A_8, A_278, B_279]: (v1_relat_1(A_8) | ~r1_tarski(A_8, k2_zfmisc_1(A_278, B_279)))), inference(resolution, [status(thm)], [c_18, c_2281])).
% 4.42/1.93  tff(c_2446, plain, (![B_316]: (v1_relat_1(B_316) | ~v1_xboole_0(B_316))), inference(resolution, [status(thm)], [c_2421, c_2289])).
% 4.42/1.93  tff(c_2450, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_2446])).
% 4.42/1.93  tff(c_2316, plain, (![C_287, A_288, B_289]: (v4_relat_1(C_287, A_288) | ~m1_subset_1(C_287, k1_zfmisc_1(k2_zfmisc_1(A_288, B_289))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.42/1.93  tff(c_2324, plain, (![A_8, A_288, B_289]: (v4_relat_1(A_8, A_288) | ~r1_tarski(A_8, k2_zfmisc_1(A_288, B_289)))), inference(resolution, [status(thm)], [c_18, c_2316])).
% 4.42/1.93  tff(c_2443, plain, (![B_314, A_288]: (v4_relat_1(B_314, A_288) | ~v1_xboole_0(B_314))), inference(resolution, [status(thm)], [c_2421, c_2324])).
% 4.42/1.93  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.42/1.93  tff(c_2469, plain, (![B_323, B_322]: (B_323=B_322 | ~r1_tarski(B_322, B_323) | ~v1_xboole_0(B_323))), inference(resolution, [status(thm)], [c_2421, c_10])).
% 4.42/1.93  tff(c_2585, plain, (![B_351, A_352]: (k1_relat_1(B_351)=A_352 | ~v1_xboole_0(A_352) | ~v4_relat_1(B_351, A_352) | ~v1_relat_1(B_351))), inference(resolution, [status(thm)], [c_24, c_2469])).
% 4.42/1.93  tff(c_2673, plain, (![B_361, A_362]: (k1_relat_1(B_361)=A_362 | ~v1_xboole_0(A_362) | ~v1_relat_1(B_361) | ~v1_xboole_0(B_361))), inference(resolution, [status(thm)], [c_2443, c_2585])).
% 4.42/1.93  tff(c_2677, plain, (![B_363]: (k1_relat_1(B_363)=k1_xboole_0 | ~v1_relat_1(B_363) | ~v1_xboole_0(B_363))), inference(resolution, [status(thm)], [c_8, c_2673])).
% 4.42/1.93  tff(c_2680, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_2677])).
% 4.42/1.93  tff(c_2683, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2450, c_2680])).
% 4.42/1.93  tff(c_2420, plain, (![B_7, B_313]: (~v1_xboole_0(B_7) | r1_tarski(B_7, B_313))), inference(resolution, [status(thm)], [c_14, c_2411])).
% 4.42/1.93  tff(c_2451, plain, (![B_317, A_318]: (v4_relat_1(B_317, A_318) | ~r1_tarski(k1_relat_1(B_317), A_318) | ~v1_relat_1(B_317))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.42/1.93  tff(c_2463, plain, (![B_317, B_313]: (v4_relat_1(B_317, B_313) | ~v1_relat_1(B_317) | ~v1_xboole_0(k1_relat_1(B_317)))), inference(resolution, [status(thm)], [c_2420, c_2451])).
% 4.42/1.93  tff(c_2703, plain, (![B_313]: (v4_relat_1(k1_xboole_0, B_313) | ~v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2683, c_2463])).
% 4.42/1.93  tff(c_2722, plain, (![B_313]: (v4_relat_1(k1_xboole_0, B_313))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2450, c_2703])).
% 4.42/1.93  tff(c_2712, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13) | ~v4_relat_1(k1_xboole_0, A_13) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2683, c_24])).
% 4.42/1.93  tff(c_2728, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13) | ~v4_relat_1(k1_xboole_0, A_13))), inference(demodulation, [status(thm), theory('equality')], [c_2450, c_2712])).
% 4.42/1.93  tff(c_2748, plain, (![A_367]: (r1_tarski(k1_xboole_0, A_367))), inference(demodulation, [status(thm), theory('equality')], [c_2722, c_2728])).
% 4.42/1.93  tff(c_2376, plain, (![C_304, B_305, A_306]: (r2_hidden(C_304, B_305) | ~r2_hidden(C_304, A_306) | ~r1_tarski(A_306, B_305))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.42/1.93  tff(c_2386, plain, (![B_307]: (r2_hidden('#skF_6', B_307) | ~r1_tarski('#skF_4', B_307))), inference(resolution, [status(thm)], [c_2259, c_2376])).
% 4.42/1.93  tff(c_2357, plain, (![B_9, A_299, A_8]: (~v1_xboole_0(B_9) | ~r2_hidden(A_299, A_8) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_18, c_2352])).
% 4.42/1.93  tff(c_2392, plain, (![B_9, B_307]: (~v1_xboole_0(B_9) | ~r1_tarski(B_307, B_9) | ~r1_tarski('#skF_4', B_307))), inference(resolution, [status(thm)], [c_2386, c_2357])).
% 4.42/1.93  tff(c_2780, plain, (![A_367]: (~v1_xboole_0(A_367) | ~r1_tarski('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_2748, c_2392])).
% 4.42/1.93  tff(c_2827, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2780])).
% 4.42/1.93  tff(c_3378, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3368, c_2827])).
% 4.42/1.93  tff(c_3390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_3378])).
% 4.42/1.93  tff(c_3392, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_3367])).
% 4.42/1.93  tff(c_2254, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_50])).
% 4.42/1.93  tff(c_3391, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_3367])).
% 4.42/1.93  tff(c_52, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.42/1.93  tff(c_2292, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2255, c_52])).
% 4.42/1.93  tff(c_54, plain, (r2_hidden('#skF_7', '#skF_4') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.42/1.93  tff(c_2257, plain, (r2_hidden('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2255, c_54])).
% 4.42/1.93  tff(c_3599, plain, (![D_427, B_428]: (k1_funct_1(k2_funct_1(D_427), k1_funct_1(D_427, '#skF_7'))='#skF_7' | k1_xboole_0=B_428 | ~v2_funct_1(D_427) | ~m1_subset_1(D_427, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_428))) | ~v1_funct_2(D_427, '#skF_4', B_428) | ~v1_funct_1(D_427))), inference(resolution, [status(thm)], [c_2257, c_3231])).
% 4.42/1.93  tff(c_3604, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_7'))='#skF_7' | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_3599])).
% 4.42/1.93  tff(c_3608, plain, ('#skF_7'='#skF_6' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_2255, c_3391, c_2292, c_3604])).
% 4.42/1.93  tff(c_3610, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3392, c_2254, c_3608])).
% 4.42/1.93  tff(c_3611, plain, (![A_367]: (~v1_xboole_0(A_367))), inference(splitRight, [status(thm)], [c_2780])).
% 4.42/1.93  tff(c_3614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3611, c_8])).
% 4.42/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/1.93  
% 4.42/1.93  Inference rules
% 4.42/1.93  ----------------------
% 4.42/1.93  #Ref     : 4
% 4.42/1.93  #Sup     : 716
% 4.42/1.93  #Fact    : 0
% 4.42/1.93  #Define  : 0
% 4.42/1.93  #Split   : 18
% 4.42/1.93  #Chain   : 0
% 4.42/1.93  #Close   : 0
% 4.42/1.93  
% 4.42/1.93  Ordering : KBO
% 4.42/1.93  
% 4.42/1.93  Simplification rules
% 4.42/1.93  ----------------------
% 4.42/1.93  #Subsume      : 261
% 4.42/1.93  #Demod        : 612
% 4.42/1.93  #Tautology    : 249
% 4.42/1.93  #SimpNegUnit  : 11
% 4.42/1.93  #BackRed      : 22
% 4.42/1.93  
% 4.42/1.93  #Partial instantiations: 0
% 4.42/1.93  #Strategies tried      : 1
% 4.42/1.93  
% 4.42/1.93  Timing (in seconds)
% 4.42/1.93  ----------------------
% 4.42/1.93  Preprocessing        : 0.33
% 4.42/1.93  Parsing              : 0.17
% 4.42/1.93  CNF conversion       : 0.02
% 4.42/1.93  Main loop            : 0.73
% 4.42/1.93  Inferencing          : 0.26
% 4.42/1.93  Reduction            : 0.23
% 4.42/1.93  Demodulation         : 0.16
% 4.42/1.93  BG Simplification    : 0.03
% 4.42/1.93  Subsumption          : 0.15
% 4.42/1.93  Abstraction          : 0.03
% 4.42/1.93  MUC search           : 0.00
% 4.42/1.93  Cooper               : 0.00
% 4.42/1.93  Total                : 1.11
% 4.42/1.93  Index Insertion      : 0.00
% 4.42/1.93  Index Deletion       : 0.00
% 4.42/1.93  Index Matching       : 0.00
% 4.42/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
