%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:21 EST 2020

% Result     : Theorem 28.11s
% Output     : CNFRefutation 28.26s
% Verified   : 
% Statistics : Number of formulae       :  148 (1295 expanded)
%              Number of leaves         :   44 ( 461 expanded)
%              Depth                    :   18
%              Number of atoms          :  257 (3036 expanded)
%              Number of equality atoms :   66 ( 731 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   1 average)

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

tff(f_133,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_114,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_50,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(c_76,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_137,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_relat_1(C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_145,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_137])).

tff(c_2556,plain,(
    ! [A_211,B_212,C_213,D_214] :
      ( k7_relset_1(A_211,B_212,C_213,D_214) = k9_relat_1(C_213,D_214)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_211,B_212))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2563,plain,(
    ! [D_214] : k7_relset_1('#skF_7','#skF_8','#skF_10',D_214) = k9_relat_1('#skF_10',D_214) ),
    inference(resolution,[status(thm)],[c_76,c_2556])).

tff(c_74,plain,(
    r2_hidden('#skF_11',k7_relset_1('#skF_7','#skF_8','#skF_10','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2951,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2563,c_74])).

tff(c_3592,plain,(
    ! [A_227,B_228,C_229] :
      ( r2_hidden(k4_tarski('#skF_6'(A_227,B_228,C_229),A_227),C_229)
      | ~ r2_hidden(A_227,k9_relat_1(C_229,B_228))
      | ~ v1_relat_1(C_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78904,plain,(
    ! [C_1293,A_1294,B_1295] :
      ( ~ v1_xboole_0(C_1293)
      | ~ r2_hidden(A_1294,k9_relat_1(C_1293,B_1295))
      | ~ v1_relat_1(C_1293) ) ),
    inference(resolution,[status(thm)],[c_3592,c_2])).

tff(c_78924,plain,
    ( ~ v1_xboole_0('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_2951,c_78904])).

tff(c_78966,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_78924])).

tff(c_80,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_50,plain,(
    ! [C_39,A_37,B_38] :
      ( k1_funct_1(C_39,A_37) = B_38
      | ~ r2_hidden(k4_tarski(A_37,B_38),C_39)
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_62111,plain,(
    ! [C_1009,A_1010,B_1011] :
      ( k1_funct_1(C_1009,'#skF_6'(A_1010,B_1011,C_1009)) = A_1010
      | ~ v1_funct_1(C_1009)
      | ~ r2_hidden(A_1010,k9_relat_1(C_1009,B_1011))
      | ~ v1_relat_1(C_1009) ) ),
    inference(resolution,[status(thm)],[c_3592,c_50])).

tff(c_62177,plain,
    ( k1_funct_1('#skF_10','#skF_6'('#skF_11','#skF_9','#skF_10')) = '#skF_11'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_2951,c_62111])).

tff(c_62219,plain,(
    k1_funct_1('#skF_10','#skF_6'('#skF_11','#skF_9','#skF_10')) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_80,c_62177])).

tff(c_42,plain,(
    ! [A_31,B_32,C_33] :
      ( r2_hidden('#skF_6'(A_31,B_32,C_33),B_32)
      | ~ r2_hidden(A_31,k9_relat_1(C_33,B_32))
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_78,plain,(
    v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_400,plain,(
    ! [A_103,B_104,C_105] :
      ( k1_relset_1(A_103,B_104,C_105) = k1_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_410,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_76,c_400])).

tff(c_43040,plain,(
    ! [B_791,A_792,C_793] :
      ( k1_xboole_0 = B_791
      | k1_relset_1(A_792,B_791,C_793) = A_792
      | ~ v1_funct_2(C_793,A_792,B_791)
      | ~ m1_subset_1(C_793,k1_zfmisc_1(k2_zfmisc_1(A_792,B_791))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_43043,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_76,c_43040])).

tff(c_43052,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_410,c_43043])).

tff(c_43054,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_43052])).

tff(c_46,plain,(
    ! [A_31,B_32,C_33] :
      ( r2_hidden('#skF_6'(A_31,B_32,C_33),k1_relat_1(C_33))
      | ~ r2_hidden(A_31,k9_relat_1(C_33,B_32))
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_43059,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_6'(A_31,B_32,'#skF_10'),'#skF_7')
      | ~ r2_hidden(A_31,k9_relat_1('#skF_10',B_32))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43054,c_46])).

tff(c_66911,plain,(
    ! [A_1071,B_1072] :
      ( r2_hidden('#skF_6'(A_1071,B_1072,'#skF_10'),'#skF_7')
      | ~ r2_hidden(A_1071,k9_relat_1('#skF_10',B_1072)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_43059])).

tff(c_72,plain,(
    ! [F_57] :
      ( k1_funct_1('#skF_10',F_57) != '#skF_11'
      | ~ r2_hidden(F_57,'#skF_9')
      | ~ r2_hidden(F_57,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_66932,plain,(
    ! [A_1073,B_1074] :
      ( k1_funct_1('#skF_10','#skF_6'(A_1073,B_1074,'#skF_10')) != '#skF_11'
      | ~ r2_hidden('#skF_6'(A_1073,B_1074,'#skF_10'),'#skF_9')
      | ~ r2_hidden(A_1073,k9_relat_1('#skF_10',B_1074)) ) ),
    inference(resolution,[status(thm)],[c_66911,c_72])).

tff(c_66936,plain,(
    ! [A_31] :
      ( k1_funct_1('#skF_10','#skF_6'(A_31,'#skF_9','#skF_10')) != '#skF_11'
      | ~ r2_hidden(A_31,k9_relat_1('#skF_10','#skF_9'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_42,c_66932])).

tff(c_68443,plain,(
    ! [A_1095] :
      ( k1_funct_1('#skF_10','#skF_6'(A_1095,'#skF_9','#skF_10')) != '#skF_11'
      | ~ r2_hidden(A_1095,k9_relat_1('#skF_10','#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_66936])).

tff(c_68478,plain,(
    k1_funct_1('#skF_10','#skF_6'('#skF_11','#skF_9','#skF_10')) != '#skF_11' ),
    inference(resolution,[status(thm)],[c_2951,c_68443])).

tff(c_68524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62219,c_68478])).

tff(c_68525,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_43052])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_68578,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68525,c_6])).

tff(c_28,plain,(
    ! [A_24] : k2_zfmisc_1(A_24,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_68576,plain,(
    ! [A_24] : k2_zfmisc_1(A_24,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68525,c_68525,c_28])).

tff(c_68910,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68576,c_76])).

tff(c_62,plain,(
    ! [C_52,A_50] :
      ( k1_xboole_0 = C_52
      | ~ v1_funct_2(C_52,A_50,k1_xboole_0)
      | k1_xboole_0 = A_50
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_83,plain,(
    ! [C_52,A_50] :
      ( k1_xboole_0 = C_52
      | ~ v1_funct_2(C_52,A_50,k1_xboole_0)
      | k1_xboole_0 = A_50
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_62])).

tff(c_77340,plain,(
    ! [C_1254,A_1255] :
      ( C_1254 = '#skF_8'
      | ~ v1_funct_2(C_1254,A_1255,'#skF_8')
      | A_1255 = '#skF_8'
      | ~ m1_subset_1(C_1254,k1_zfmisc_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68525,c_68525,c_68525,c_68525,c_83])).

tff(c_77342,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_7' = '#skF_8'
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_78,c_77340])).

tff(c_77345,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68910,c_77342])).

tff(c_77346,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_77345])).

tff(c_34,plain,(
    ! [A_27] : ~ v1_xboole_0(k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ! [A_26] : k3_tarski(k1_zfmisc_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_170,plain,(
    ! [C_75,A_76,D_77] :
      ( r2_hidden(C_75,k3_tarski(A_76))
      | ~ r2_hidden(D_77,A_76)
      | ~ r2_hidden(C_75,D_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_180,plain,(
    ! [C_78,A_79] :
      ( r2_hidden(C_78,k3_tarski(A_79))
      | ~ r2_hidden(C_78,'#skF_1'(A_79))
      | v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_4,c_170])).

tff(c_356,plain,(
    ! [A_99,C_100] :
      ( ~ v1_xboole_0(k3_tarski(A_99))
      | ~ r2_hidden(C_100,'#skF_1'(A_99))
      | v1_xboole_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_180,c_2])).

tff(c_378,plain,(
    ! [A_101] :
      ( ~ v1_xboole_0(k3_tarski(A_101))
      | v1_xboole_0(A_101)
      | v1_xboole_0('#skF_1'(A_101)) ) ),
    inference(resolution,[status(thm)],[c_4,c_356])).

tff(c_390,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(A_26)
      | v1_xboole_0(k1_zfmisc_1(A_26))
      | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_26))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_378])).

tff(c_394,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(A_26)
      | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_26))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_390])).

tff(c_937,plain,(
    ! [A_183,B_184] :
      ( r2_hidden('#skF_3'(A_183,B_184),A_183)
      | r2_hidden('#skF_4'(A_183,B_184),B_184)
      | k3_tarski(A_183) = B_184 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1082,plain,(
    ! [A_185,B_186] :
      ( ~ v1_xboole_0(A_185)
      | r2_hidden('#skF_4'(A_185,B_186),B_186)
      | k3_tarski(A_185) = B_186 ) ),
    inference(resolution,[status(thm)],[c_937,c_2])).

tff(c_1158,plain,(
    ! [B_187,A_188] :
      ( ~ v1_xboole_0(B_187)
      | ~ v1_xboole_0(A_188)
      | k3_tarski(A_188) = B_187 ) ),
    inference(resolution,[status(thm)],[c_1082,c_2])).

tff(c_1210,plain,(
    ! [A_189] :
      ( ~ v1_xboole_0(A_189)
      | k3_tarski(A_189) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_1158])).

tff(c_1278,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1210])).

tff(c_22,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_3'(A_5,B_6),A_5)
      | r2_hidden('#skF_4'(A_5,B_6),B_6)
      | k3_tarski(A_5) = B_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [A_5,C_20] :
      ( r2_hidden('#skF_5'(A_5,k3_tarski(A_5),C_20),A_5)
      | ~ r2_hidden(C_20,k3_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_192,plain,(
    ! [A_80,C_81] :
      ( r2_hidden('#skF_5'(A_80,k3_tarski(A_80),C_81),A_80)
      | ~ r2_hidden(C_81,k3_tarski(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_209,plain,(
    ! [A_82,C_83] :
      ( ~ v1_xboole_0(A_82)
      | ~ r2_hidden(C_83,k3_tarski(A_82)) ) ),
    inference(resolution,[status(thm)],[c_192,c_2])).

tff(c_256,plain,(
    ! [A_87,C_88] :
      ( ~ v1_xboole_0(A_87)
      | ~ r2_hidden(C_88,k3_tarski(k3_tarski(A_87))) ) ),
    inference(resolution,[status(thm)],[c_10,c_209])).

tff(c_308,plain,(
    ! [A_93,C_94] :
      ( ~ v1_xboole_0(A_93)
      | ~ r2_hidden(C_94,k3_tarski(k3_tarski(k3_tarski(A_93)))) ) ),
    inference(resolution,[status(thm)],[c_10,c_256])).

tff(c_328,plain,(
    ! [A_93,C_20] :
      ( ~ v1_xboole_0(A_93)
      | ~ r2_hidden(C_20,k3_tarski(k3_tarski(k3_tarski(k3_tarski(A_93))))) ) ),
    inference(resolution,[status(thm)],[c_10,c_308])).

tff(c_1338,plain,(
    ! [C_20] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(C_20,k3_tarski(k3_tarski(k3_tarski(k1_xboole_0)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1278,c_328])).

tff(c_1439,plain,(
    ! [C_191] : ~ r2_hidden(C_191,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1278,c_1278,c_1278,c_6,c_1338])).

tff(c_1447,plain,(
    ! [B_6] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_6),B_6)
      | k3_tarski(k1_xboole_0) = B_6 ) ),
    inference(resolution,[status(thm)],[c_22,c_1439])).

tff(c_3347,plain,(
    ! [B_225] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_225),B_225)
      | k1_xboole_0 = B_225 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1278,c_1447])).

tff(c_3431,plain,(
    ! [B_226] :
      ( ~ v1_xboole_0(B_226)
      | k1_xboole_0 = B_226 ) ),
    inference(resolution,[status(thm)],[c_3347,c_2])).

tff(c_41074,plain,(
    ! [A_756] :
      ( '#skF_1'(k1_zfmisc_1(A_756)) = k1_xboole_0
      | ~ v1_xboole_0(A_756) ) ),
    inference(resolution,[status(thm)],[c_394,c_3431])).

tff(c_188,plain,(
    ! [C_78,A_26] :
      ( r2_hidden(C_78,A_26)
      | ~ r2_hidden(C_78,'#skF_1'(k1_zfmisc_1(A_26)))
      | v1_xboole_0(k1_zfmisc_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_180])).

tff(c_292,plain,(
    ! [C_91,A_92] :
      ( r2_hidden(C_91,A_92)
      | ~ r2_hidden(C_91,'#skF_1'(k1_zfmisc_1(A_92))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_188])).

tff(c_500,plain,(
    ! [A_125] :
      ( r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1(A_125))),A_125)
      | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_125))) ) ),
    inference(resolution,[status(thm)],[c_4,c_292])).

tff(c_546,plain,
    ( k1_funct_1('#skF_10','#skF_1'('#skF_1'(k1_zfmisc_1('#skF_7')))) != '#skF_11'
    | ~ r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1('#skF_7'))),'#skF_9')
    | v1_xboole_0('#skF_1'(k1_zfmisc_1('#skF_7'))) ),
    inference(resolution,[status(thm)],[c_500,c_72])).

tff(c_598,plain,(
    ~ r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1('#skF_7'))),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_546])).

tff(c_41128,plain,
    ( ~ r2_hidden('#skF_1'(k1_xboole_0),'#skF_9')
    | ~ v1_xboole_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_41074,c_598])).

tff(c_41218,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_41128])).

tff(c_77361,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77346,c_41218])).

tff(c_77383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68578,c_77361])).

tff(c_77384,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_77345])).

tff(c_69397,plain,(
    ! [C_1115,A_1116,B_1117] :
      ( ~ v1_xboole_0(C_1115)
      | ~ r2_hidden(A_1116,k9_relat_1(C_1115,B_1117))
      | ~ v1_relat_1(C_1115) ) ),
    inference(resolution,[status(thm)],[c_3592,c_2])).

tff(c_69424,plain,
    ( ~ v1_xboole_0('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_2951,c_69397])).

tff(c_69469,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_69424])).

tff(c_77398,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77384,c_69469])).

tff(c_77433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68578,c_77398])).

tff(c_77435,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_41128])).

tff(c_3430,plain,(
    ! [B_225] :
      ( ~ v1_xboole_0(B_225)
      | k1_xboole_0 = B_225 ) ),
    inference(resolution,[status(thm)],[c_3347,c_2])).

tff(c_77456,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_77435,c_3430])).

tff(c_30,plain,(
    ! [B_25] : k2_zfmisc_1(k1_xboole_0,B_25) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_77492,plain,(
    ! [B_25] : k2_zfmisc_1('#skF_7',B_25) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77456,c_77456,c_30])).

tff(c_77995,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77492,c_76])).

tff(c_36,plain,(
    ! [A_28,B_29] :
      ( r2_hidden(A_28,B_29)
      | v1_xboole_0(B_29)
      | ~ m1_subset_1(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_82298,plain,(
    ! [C_1347,B_1348,A_1349] :
      ( r2_hidden(C_1347,k3_tarski(B_1348))
      | ~ r2_hidden(C_1347,A_1349)
      | v1_xboole_0(B_1348)
      | ~ m1_subset_1(A_1349,B_1348) ) ),
    inference(resolution,[status(thm)],[c_36,c_170])).

tff(c_127817,plain,(
    ! [A_1830,B_1831] :
      ( r2_hidden('#skF_1'(A_1830),k3_tarski(B_1831))
      | v1_xboole_0(B_1831)
      | ~ m1_subset_1(A_1830,B_1831)
      | v1_xboole_0(A_1830) ) ),
    inference(resolution,[status(thm)],[c_4,c_82298])).

tff(c_128070,plain,(
    ! [A_1830,A_26] :
      ( r2_hidden('#skF_1'(A_1830),A_26)
      | v1_xboole_0(k1_zfmisc_1(A_26))
      | ~ m1_subset_1(A_1830,k1_zfmisc_1(A_26))
      | v1_xboole_0(A_1830) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_127817])).

tff(c_131990,plain,(
    ! [A_1851,A_1852] :
      ( r2_hidden('#skF_1'(A_1851),A_1852)
      | ~ m1_subset_1(A_1851,k1_zfmisc_1(A_1852))
      | v1_xboole_0(A_1851) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_128070])).

tff(c_1414,plain,(
    ! [C_20] : ~ r2_hidden(C_20,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1278,c_1278,c_1278,c_6,c_1338])).

tff(c_77481,plain,(
    ! [C_20] : ~ r2_hidden(C_20,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77456,c_1414])).

tff(c_132299,plain,(
    ! [A_1853] :
      ( ~ m1_subset_1(A_1853,k1_zfmisc_1('#skF_7'))
      | v1_xboole_0(A_1853) ) ),
    inference(resolution,[status(thm)],[c_131990,c_77481])).

tff(c_132302,plain,(
    v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_77995,c_132299])).

tff(c_132306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78966,c_132302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:08:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 28.11/17.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.11/17.90  
% 28.11/17.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.11/17.90  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 28.11/17.90  
% 28.11/17.90  %Foreground sorts:
% 28.11/17.90  
% 28.11/17.90  
% 28.11/17.90  %Background operators:
% 28.11/17.90  
% 28.11/17.90  
% 28.11/17.90  %Foreground operators:
% 28.11/17.90  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 28.11/17.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 28.11/17.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 28.11/17.90  tff('#skF_11', type, '#skF_11': $i).
% 28.11/17.90  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 28.11/17.90  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 28.11/17.90  tff('#skF_1', type, '#skF_1': $i > $i).
% 28.11/17.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 28.11/17.90  tff('#skF_7', type, '#skF_7': $i).
% 28.11/17.90  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 28.11/17.90  tff('#skF_10', type, '#skF_10': $i).
% 28.11/17.90  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 28.11/17.90  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 28.11/17.90  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 28.11/17.90  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 28.11/17.90  tff('#skF_9', type, '#skF_9': $i).
% 28.11/17.90  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 28.11/17.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 28.11/17.90  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 28.11/17.90  tff('#skF_8', type, '#skF_8': $i).
% 28.11/17.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 28.11/17.90  tff(k3_tarski, type, k3_tarski: $i > $i).
% 28.11/17.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 28.11/17.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 28.11/17.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 28.11/17.90  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 28.11/17.90  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 28.11/17.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 28.11/17.90  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 28.11/17.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 28.11/17.90  
% 28.26/17.92  tff(f_133, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 28.26/17.92  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 28.26/17.92  tff(f_96, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 28.26/17.92  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 28.26/17.92  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 28.26/17.92  tff(f_84, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 28.26/17.92  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 28.26/17.92  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 28.26/17.92  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 28.26/17.92  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 28.26/17.92  tff(f_53, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 28.26/17.92  tff(f_50, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 28.26/17.92  tff(f_42, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 28.26/17.92  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 28.26/17.92  tff(c_76, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 28.26/17.92  tff(c_137, plain, (![C_68, A_69, B_70]: (v1_relat_1(C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 28.26/17.92  tff(c_145, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_137])).
% 28.26/17.92  tff(c_2556, plain, (![A_211, B_212, C_213, D_214]: (k7_relset_1(A_211, B_212, C_213, D_214)=k9_relat_1(C_213, D_214) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_211, B_212))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 28.26/17.92  tff(c_2563, plain, (![D_214]: (k7_relset_1('#skF_7', '#skF_8', '#skF_10', D_214)=k9_relat_1('#skF_10', D_214))), inference(resolution, [status(thm)], [c_76, c_2556])).
% 28.26/17.92  tff(c_74, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_7', '#skF_8', '#skF_10', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 28.26/17.92  tff(c_2951, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2563, c_74])).
% 28.26/17.92  tff(c_3592, plain, (![A_227, B_228, C_229]: (r2_hidden(k4_tarski('#skF_6'(A_227, B_228, C_229), A_227), C_229) | ~r2_hidden(A_227, k9_relat_1(C_229, B_228)) | ~v1_relat_1(C_229))), inference(cnfTransformation, [status(thm)], [f_74])).
% 28.26/17.92  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 28.26/17.92  tff(c_78904, plain, (![C_1293, A_1294, B_1295]: (~v1_xboole_0(C_1293) | ~r2_hidden(A_1294, k9_relat_1(C_1293, B_1295)) | ~v1_relat_1(C_1293))), inference(resolution, [status(thm)], [c_3592, c_2])).
% 28.26/17.92  tff(c_78924, plain, (~v1_xboole_0('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_2951, c_78904])).
% 28.26/17.92  tff(c_78966, plain, (~v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_78924])).
% 28.26/17.92  tff(c_80, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_133])).
% 28.26/17.92  tff(c_50, plain, (![C_39, A_37, B_38]: (k1_funct_1(C_39, A_37)=B_38 | ~r2_hidden(k4_tarski(A_37, B_38), C_39) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_84])).
% 28.26/17.92  tff(c_62111, plain, (![C_1009, A_1010, B_1011]: (k1_funct_1(C_1009, '#skF_6'(A_1010, B_1011, C_1009))=A_1010 | ~v1_funct_1(C_1009) | ~r2_hidden(A_1010, k9_relat_1(C_1009, B_1011)) | ~v1_relat_1(C_1009))), inference(resolution, [status(thm)], [c_3592, c_50])).
% 28.26/17.92  tff(c_62177, plain, (k1_funct_1('#skF_10', '#skF_6'('#skF_11', '#skF_9', '#skF_10'))='#skF_11' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_2951, c_62111])).
% 28.26/17.92  tff(c_62219, plain, (k1_funct_1('#skF_10', '#skF_6'('#skF_11', '#skF_9', '#skF_10'))='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_80, c_62177])).
% 28.26/17.92  tff(c_42, plain, (![A_31, B_32, C_33]: (r2_hidden('#skF_6'(A_31, B_32, C_33), B_32) | ~r2_hidden(A_31, k9_relat_1(C_33, B_32)) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_74])).
% 28.26/17.92  tff(c_78, plain, (v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_133])).
% 28.26/17.92  tff(c_400, plain, (![A_103, B_104, C_105]: (k1_relset_1(A_103, B_104, C_105)=k1_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 28.26/17.92  tff(c_410, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_76, c_400])).
% 28.26/17.92  tff(c_43040, plain, (![B_791, A_792, C_793]: (k1_xboole_0=B_791 | k1_relset_1(A_792, B_791, C_793)=A_792 | ~v1_funct_2(C_793, A_792, B_791) | ~m1_subset_1(C_793, k1_zfmisc_1(k2_zfmisc_1(A_792, B_791))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 28.26/17.92  tff(c_43043, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_76, c_43040])).
% 28.26/17.92  tff(c_43052, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_410, c_43043])).
% 28.26/17.92  tff(c_43054, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_43052])).
% 28.26/17.92  tff(c_46, plain, (![A_31, B_32, C_33]: (r2_hidden('#skF_6'(A_31, B_32, C_33), k1_relat_1(C_33)) | ~r2_hidden(A_31, k9_relat_1(C_33, B_32)) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_74])).
% 28.26/17.92  tff(c_43059, plain, (![A_31, B_32]: (r2_hidden('#skF_6'(A_31, B_32, '#skF_10'), '#skF_7') | ~r2_hidden(A_31, k9_relat_1('#skF_10', B_32)) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_43054, c_46])).
% 28.26/17.92  tff(c_66911, plain, (![A_1071, B_1072]: (r2_hidden('#skF_6'(A_1071, B_1072, '#skF_10'), '#skF_7') | ~r2_hidden(A_1071, k9_relat_1('#skF_10', B_1072)))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_43059])).
% 28.26/17.92  tff(c_72, plain, (![F_57]: (k1_funct_1('#skF_10', F_57)!='#skF_11' | ~r2_hidden(F_57, '#skF_9') | ~r2_hidden(F_57, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 28.26/17.92  tff(c_66932, plain, (![A_1073, B_1074]: (k1_funct_1('#skF_10', '#skF_6'(A_1073, B_1074, '#skF_10'))!='#skF_11' | ~r2_hidden('#skF_6'(A_1073, B_1074, '#skF_10'), '#skF_9') | ~r2_hidden(A_1073, k9_relat_1('#skF_10', B_1074)))), inference(resolution, [status(thm)], [c_66911, c_72])).
% 28.26/17.92  tff(c_66936, plain, (![A_31]: (k1_funct_1('#skF_10', '#skF_6'(A_31, '#skF_9', '#skF_10'))!='#skF_11' | ~r2_hidden(A_31, k9_relat_1('#skF_10', '#skF_9')) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_42, c_66932])).
% 28.26/17.92  tff(c_68443, plain, (![A_1095]: (k1_funct_1('#skF_10', '#skF_6'(A_1095, '#skF_9', '#skF_10'))!='#skF_11' | ~r2_hidden(A_1095, k9_relat_1('#skF_10', '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_66936])).
% 28.26/17.92  tff(c_68478, plain, (k1_funct_1('#skF_10', '#skF_6'('#skF_11', '#skF_9', '#skF_10'))!='#skF_11'), inference(resolution, [status(thm)], [c_2951, c_68443])).
% 28.26/17.92  tff(c_68524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62219, c_68478])).
% 28.26/17.92  tff(c_68525, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_43052])).
% 28.26/17.92  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 28.26/17.92  tff(c_68578, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_68525, c_6])).
% 28.26/17.92  tff(c_28, plain, (![A_24]: (k2_zfmisc_1(A_24, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 28.26/17.92  tff(c_68576, plain, (![A_24]: (k2_zfmisc_1(A_24, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_68525, c_68525, c_28])).
% 28.26/17.92  tff(c_68910, plain, (m1_subset_1('#skF_10', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_68576, c_76])).
% 28.26/17.92  tff(c_62, plain, (![C_52, A_50]: (k1_xboole_0=C_52 | ~v1_funct_2(C_52, A_50, k1_xboole_0) | k1_xboole_0=A_50 | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 28.26/17.92  tff(c_83, plain, (![C_52, A_50]: (k1_xboole_0=C_52 | ~v1_funct_2(C_52, A_50, k1_xboole_0) | k1_xboole_0=A_50 | ~m1_subset_1(C_52, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_62])).
% 28.26/17.92  tff(c_77340, plain, (![C_1254, A_1255]: (C_1254='#skF_8' | ~v1_funct_2(C_1254, A_1255, '#skF_8') | A_1255='#skF_8' | ~m1_subset_1(C_1254, k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_68525, c_68525, c_68525, c_68525, c_83])).
% 28.26/17.92  tff(c_77342, plain, ('#skF_10'='#skF_8' | '#skF_7'='#skF_8' | ~m1_subset_1('#skF_10', k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_78, c_77340])).
% 28.26/17.92  tff(c_77345, plain, ('#skF_10'='#skF_8' | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_68910, c_77342])).
% 28.26/17.92  tff(c_77346, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_77345])).
% 28.26/17.92  tff(c_34, plain, (![A_27]: (~v1_xboole_0(k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 28.26/17.92  tff(c_32, plain, (![A_26]: (k3_tarski(k1_zfmisc_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_50])).
% 28.26/17.92  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 28.26/17.92  tff(c_170, plain, (![C_75, A_76, D_77]: (r2_hidden(C_75, k3_tarski(A_76)) | ~r2_hidden(D_77, A_76) | ~r2_hidden(C_75, D_77))), inference(cnfTransformation, [status(thm)], [f_42])).
% 28.26/17.92  tff(c_180, plain, (![C_78, A_79]: (r2_hidden(C_78, k3_tarski(A_79)) | ~r2_hidden(C_78, '#skF_1'(A_79)) | v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_4, c_170])).
% 28.26/17.92  tff(c_356, plain, (![A_99, C_100]: (~v1_xboole_0(k3_tarski(A_99)) | ~r2_hidden(C_100, '#skF_1'(A_99)) | v1_xboole_0(A_99))), inference(resolution, [status(thm)], [c_180, c_2])).
% 28.26/17.92  tff(c_378, plain, (![A_101]: (~v1_xboole_0(k3_tarski(A_101)) | v1_xboole_0(A_101) | v1_xboole_0('#skF_1'(A_101)))), inference(resolution, [status(thm)], [c_4, c_356])).
% 28.26/17.92  tff(c_390, plain, (![A_26]: (~v1_xboole_0(A_26) | v1_xboole_0(k1_zfmisc_1(A_26)) | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_26))))), inference(superposition, [status(thm), theory('equality')], [c_32, c_378])).
% 28.26/17.92  tff(c_394, plain, (![A_26]: (~v1_xboole_0(A_26) | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_26))))), inference(negUnitSimplification, [status(thm)], [c_34, c_390])).
% 28.26/17.92  tff(c_937, plain, (![A_183, B_184]: (r2_hidden('#skF_3'(A_183, B_184), A_183) | r2_hidden('#skF_4'(A_183, B_184), B_184) | k3_tarski(A_183)=B_184)), inference(cnfTransformation, [status(thm)], [f_42])).
% 28.26/17.92  tff(c_1082, plain, (![A_185, B_186]: (~v1_xboole_0(A_185) | r2_hidden('#skF_4'(A_185, B_186), B_186) | k3_tarski(A_185)=B_186)), inference(resolution, [status(thm)], [c_937, c_2])).
% 28.26/17.92  tff(c_1158, plain, (![B_187, A_188]: (~v1_xboole_0(B_187) | ~v1_xboole_0(A_188) | k3_tarski(A_188)=B_187)), inference(resolution, [status(thm)], [c_1082, c_2])).
% 28.26/17.92  tff(c_1210, plain, (![A_189]: (~v1_xboole_0(A_189) | k3_tarski(A_189)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_1158])).
% 28.26/17.92  tff(c_1278, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1210])).
% 28.26/17.92  tff(c_22, plain, (![A_5, B_6]: (r2_hidden('#skF_3'(A_5, B_6), A_5) | r2_hidden('#skF_4'(A_5, B_6), B_6) | k3_tarski(A_5)=B_6)), inference(cnfTransformation, [status(thm)], [f_42])).
% 28.26/17.92  tff(c_10, plain, (![A_5, C_20]: (r2_hidden('#skF_5'(A_5, k3_tarski(A_5), C_20), A_5) | ~r2_hidden(C_20, k3_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 28.26/17.92  tff(c_192, plain, (![A_80, C_81]: (r2_hidden('#skF_5'(A_80, k3_tarski(A_80), C_81), A_80) | ~r2_hidden(C_81, k3_tarski(A_80)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 28.26/17.92  tff(c_209, plain, (![A_82, C_83]: (~v1_xboole_0(A_82) | ~r2_hidden(C_83, k3_tarski(A_82)))), inference(resolution, [status(thm)], [c_192, c_2])).
% 28.26/17.92  tff(c_256, plain, (![A_87, C_88]: (~v1_xboole_0(A_87) | ~r2_hidden(C_88, k3_tarski(k3_tarski(A_87))))), inference(resolution, [status(thm)], [c_10, c_209])).
% 28.26/17.92  tff(c_308, plain, (![A_93, C_94]: (~v1_xboole_0(A_93) | ~r2_hidden(C_94, k3_tarski(k3_tarski(k3_tarski(A_93)))))), inference(resolution, [status(thm)], [c_10, c_256])).
% 28.26/17.92  tff(c_328, plain, (![A_93, C_20]: (~v1_xboole_0(A_93) | ~r2_hidden(C_20, k3_tarski(k3_tarski(k3_tarski(k3_tarski(A_93))))))), inference(resolution, [status(thm)], [c_10, c_308])).
% 28.26/17.92  tff(c_1338, plain, (![C_20]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(C_20, k3_tarski(k3_tarski(k3_tarski(k1_xboole_0)))))), inference(superposition, [status(thm), theory('equality')], [c_1278, c_328])).
% 28.26/17.92  tff(c_1439, plain, (![C_191]: (~r2_hidden(C_191, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1278, c_1278, c_1278, c_6, c_1338])).
% 28.26/17.92  tff(c_1447, plain, (![B_6]: (r2_hidden('#skF_4'(k1_xboole_0, B_6), B_6) | k3_tarski(k1_xboole_0)=B_6)), inference(resolution, [status(thm)], [c_22, c_1439])).
% 28.26/17.92  tff(c_3347, plain, (![B_225]: (r2_hidden('#skF_4'(k1_xboole_0, B_225), B_225) | k1_xboole_0=B_225)), inference(demodulation, [status(thm), theory('equality')], [c_1278, c_1447])).
% 28.26/17.92  tff(c_3431, plain, (![B_226]: (~v1_xboole_0(B_226) | k1_xboole_0=B_226)), inference(resolution, [status(thm)], [c_3347, c_2])).
% 28.26/17.92  tff(c_41074, plain, (![A_756]: ('#skF_1'(k1_zfmisc_1(A_756))=k1_xboole_0 | ~v1_xboole_0(A_756))), inference(resolution, [status(thm)], [c_394, c_3431])).
% 28.26/17.92  tff(c_188, plain, (![C_78, A_26]: (r2_hidden(C_78, A_26) | ~r2_hidden(C_78, '#skF_1'(k1_zfmisc_1(A_26))) | v1_xboole_0(k1_zfmisc_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_180])).
% 28.26/17.92  tff(c_292, plain, (![C_91, A_92]: (r2_hidden(C_91, A_92) | ~r2_hidden(C_91, '#skF_1'(k1_zfmisc_1(A_92))))), inference(negUnitSimplification, [status(thm)], [c_34, c_188])).
% 28.26/17.92  tff(c_500, plain, (![A_125]: (r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1(A_125))), A_125) | v1_xboole_0('#skF_1'(k1_zfmisc_1(A_125))))), inference(resolution, [status(thm)], [c_4, c_292])).
% 28.26/17.92  tff(c_546, plain, (k1_funct_1('#skF_10', '#skF_1'('#skF_1'(k1_zfmisc_1('#skF_7'))))!='#skF_11' | ~r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1('#skF_7'))), '#skF_9') | v1_xboole_0('#skF_1'(k1_zfmisc_1('#skF_7')))), inference(resolution, [status(thm)], [c_500, c_72])).
% 28.26/17.92  tff(c_598, plain, (~r2_hidden('#skF_1'('#skF_1'(k1_zfmisc_1('#skF_7'))), '#skF_9')), inference(splitLeft, [status(thm)], [c_546])).
% 28.26/17.92  tff(c_41128, plain, (~r2_hidden('#skF_1'(k1_xboole_0), '#skF_9') | ~v1_xboole_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_41074, c_598])).
% 28.26/17.92  tff(c_41218, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_41128])).
% 28.26/17.92  tff(c_77361, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_77346, c_41218])).
% 28.26/17.92  tff(c_77383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68578, c_77361])).
% 28.26/17.92  tff(c_77384, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_77345])).
% 28.26/17.92  tff(c_69397, plain, (![C_1115, A_1116, B_1117]: (~v1_xboole_0(C_1115) | ~r2_hidden(A_1116, k9_relat_1(C_1115, B_1117)) | ~v1_relat_1(C_1115))), inference(resolution, [status(thm)], [c_3592, c_2])).
% 28.26/17.92  tff(c_69424, plain, (~v1_xboole_0('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_2951, c_69397])).
% 28.26/17.92  tff(c_69469, plain, (~v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_69424])).
% 28.26/17.92  tff(c_77398, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_77384, c_69469])).
% 28.26/17.92  tff(c_77433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68578, c_77398])).
% 28.26/17.92  tff(c_77435, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_41128])).
% 28.26/17.92  tff(c_3430, plain, (![B_225]: (~v1_xboole_0(B_225) | k1_xboole_0=B_225)), inference(resolution, [status(thm)], [c_3347, c_2])).
% 28.26/17.92  tff(c_77456, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_77435, c_3430])).
% 28.26/17.92  tff(c_30, plain, (![B_25]: (k2_zfmisc_1(k1_xboole_0, B_25)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 28.26/17.92  tff(c_77492, plain, (![B_25]: (k2_zfmisc_1('#skF_7', B_25)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_77456, c_77456, c_30])).
% 28.26/17.92  tff(c_77995, plain, (m1_subset_1('#skF_10', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_77492, c_76])).
% 28.26/17.92  tff(c_36, plain, (![A_28, B_29]: (r2_hidden(A_28, B_29) | v1_xboole_0(B_29) | ~m1_subset_1(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_59])).
% 28.26/17.92  tff(c_82298, plain, (![C_1347, B_1348, A_1349]: (r2_hidden(C_1347, k3_tarski(B_1348)) | ~r2_hidden(C_1347, A_1349) | v1_xboole_0(B_1348) | ~m1_subset_1(A_1349, B_1348))), inference(resolution, [status(thm)], [c_36, c_170])).
% 28.26/17.92  tff(c_127817, plain, (![A_1830, B_1831]: (r2_hidden('#skF_1'(A_1830), k3_tarski(B_1831)) | v1_xboole_0(B_1831) | ~m1_subset_1(A_1830, B_1831) | v1_xboole_0(A_1830))), inference(resolution, [status(thm)], [c_4, c_82298])).
% 28.26/17.92  tff(c_128070, plain, (![A_1830, A_26]: (r2_hidden('#skF_1'(A_1830), A_26) | v1_xboole_0(k1_zfmisc_1(A_26)) | ~m1_subset_1(A_1830, k1_zfmisc_1(A_26)) | v1_xboole_0(A_1830))), inference(superposition, [status(thm), theory('equality')], [c_32, c_127817])).
% 28.26/17.92  tff(c_131990, plain, (![A_1851, A_1852]: (r2_hidden('#skF_1'(A_1851), A_1852) | ~m1_subset_1(A_1851, k1_zfmisc_1(A_1852)) | v1_xboole_0(A_1851))), inference(negUnitSimplification, [status(thm)], [c_34, c_128070])).
% 28.26/17.92  tff(c_1414, plain, (![C_20]: (~r2_hidden(C_20, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1278, c_1278, c_1278, c_6, c_1338])).
% 28.26/17.92  tff(c_77481, plain, (![C_20]: (~r2_hidden(C_20, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_77456, c_1414])).
% 28.26/17.92  tff(c_132299, plain, (![A_1853]: (~m1_subset_1(A_1853, k1_zfmisc_1('#skF_7')) | v1_xboole_0(A_1853))), inference(resolution, [status(thm)], [c_131990, c_77481])).
% 28.26/17.92  tff(c_132302, plain, (v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_77995, c_132299])).
% 28.26/17.92  tff(c_132306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78966, c_132302])).
% 28.26/17.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 28.26/17.92  
% 28.26/17.92  Inference rules
% 28.26/17.92  ----------------------
% 28.26/17.92  #Ref     : 0
% 28.26/17.92  #Sup     : 34294
% 28.26/17.92  #Fact    : 0
% 28.26/17.92  #Define  : 0
% 28.26/17.92  #Split   : 53
% 28.26/17.92  #Chain   : 0
% 28.26/17.92  #Close   : 0
% 28.26/17.92  
% 28.26/17.92  Ordering : KBO
% 28.26/17.92  
% 28.26/17.92  Simplification rules
% 28.26/17.92  ----------------------
% 28.26/17.92  #Subsume      : 9976
% 28.26/17.92  #Demod        : 34958
% 28.26/17.92  #Tautology    : 13390
% 28.26/17.92  #SimpNegUnit  : 1565
% 28.26/17.92  #BackRed      : 448
% 28.26/17.92  
% 28.26/17.92  #Partial instantiations: 0
% 28.26/17.92  #Strategies tried      : 1
% 28.26/17.92  
% 28.26/17.92  Timing (in seconds)
% 28.26/17.92  ----------------------
% 28.26/17.92  Preprocessing        : 0.35
% 28.26/17.92  Parsing              : 0.17
% 28.26/17.92  CNF conversion       : 0.03
% 28.26/17.92  Main loop            : 16.79
% 28.26/17.93  Inferencing          : 2.35
% 28.26/17.93  Reduction            : 3.98
% 28.26/17.93  Demodulation         : 2.72
% 28.26/17.93  BG Simplification    : 0.28
% 28.26/17.93  Subsumption          : 9.42
% 28.26/17.93  Abstraction          : 0.48
% 28.26/17.93  MUC search           : 0.00
% 28.26/17.93  Cooper               : 0.00
% 28.26/17.93  Total                : 17.19
% 28.26/17.93  Index Insertion      : 0.00
% 28.26/17.93  Index Deletion       : 0.00
% 28.26/17.93  Index Matching       : 0.00
% 28.26/17.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
