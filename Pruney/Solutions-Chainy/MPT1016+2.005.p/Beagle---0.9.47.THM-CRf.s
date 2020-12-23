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
% DateTime   : Thu Dec  3 10:15:41 EST 2020

% Result     : Theorem 4.95s
% Output     : CNFRefutation 4.95s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 718 expanded)
%              Number of leaves         :   42 ( 259 expanded)
%              Depth                    :   17
%              Number of atoms          :  346 (2416 expanded)
%              Number of equality atoms :   84 ( 585 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
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

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_82,axiom,(
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

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_125,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_111,axiom,(
    ! [A,B] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relset_1)).

tff(f_49,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_931,plain,(
    ! [C_176,A_177,B_178] :
      ( v4_relat_1(C_176,A_177)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_945,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_931])).

tff(c_126,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_139,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_126])).

tff(c_171,plain,(
    ! [C_67,A_68,B_69] :
      ( v4_relat_1(C_67,A_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_185,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_171])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_64,plain,
    ( '#skF_7' != '#skF_6'
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_91,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_289,plain,(
    ! [A_93] :
      ( r2_hidden('#skF_3'(A_93),k1_relat_1(A_93))
      | v2_funct_1(A_93)
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_776,plain,(
    ! [A_146,B_147] :
      ( r2_hidden('#skF_3'(A_146),B_147)
      | ~ r1_tarski(k1_relat_1(A_146),B_147)
      | v2_funct_1(A_146)
      | ~ v1_funct_1(A_146)
      | ~ v1_relat_1(A_146) ) ),
    inference(resolution,[status(thm)],[c_289,c_2])).

tff(c_268,plain,(
    ! [A_91] :
      ( '#skF_2'(A_91) != '#skF_3'(A_91)
      | v2_funct_1(A_91)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_271,plain,
    ( '#skF_2'('#skF_5') != '#skF_3'('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_268,c_91])).

tff(c_274,plain,(
    '#skF_2'('#skF_5') != '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_62,c_271])).

tff(c_275,plain,(
    ! [A_92] :
      ( r2_hidden('#skF_2'(A_92),k1_relat_1(A_92))
      | v2_funct_1(A_92)
      | ~ v1_funct_1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_610,plain,(
    ! [A_128,B_129] :
      ( r2_hidden('#skF_2'(A_128),B_129)
      | ~ r1_tarski(k1_relat_1(A_128),B_129)
      | v2_funct_1(A_128)
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(resolution,[status(thm)],[c_275,c_2])).

tff(c_470,plain,(
    ! [A_115] :
      ( k1_funct_1(A_115,'#skF_2'(A_115)) = k1_funct_1(A_115,'#skF_3'(A_115))
      | v2_funct_1(A_115)
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_82,plain,(
    ! [D_45,C_44] :
      ( v2_funct_1('#skF_5')
      | D_45 = C_44
      | k1_funct_1('#skF_5',D_45) != k1_funct_1('#skF_5',C_44)
      | ~ r2_hidden(D_45,'#skF_4')
      | ~ r2_hidden(C_44,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_187,plain,(
    ! [D_45,C_44] :
      ( D_45 = C_44
      | k1_funct_1('#skF_5',D_45) != k1_funct_1('#skF_5',C_44)
      | ~ r2_hidden(D_45,'#skF_4')
      | ~ r2_hidden(C_44,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_82])).

tff(c_479,plain,(
    ! [D_45] :
      ( D_45 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_45) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_45,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_187])).

tff(c_488,plain,(
    ! [D_45] :
      ( D_45 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_45) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_45,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_62,c_479])).

tff(c_489,plain,(
    ! [D_45] :
      ( D_45 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_45) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_45,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_488])).

tff(c_609,plain,(
    ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_489])).

tff(c_613,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_610,c_609])).

tff(c_621,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_62,c_613])).

tff(c_622,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_621])).

tff(c_630,plain,
    ( ~ v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_622])).

tff(c_637,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_185,c_630])).

tff(c_639,plain,(
    r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_489])).

tff(c_476,plain,(
    ! [C_44] :
      ( C_44 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_44) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_44,'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_187])).

tff(c_485,plain,(
    ! [C_44] :
      ( C_44 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_44) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_44,'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_62,c_476])).

tff(c_486,plain,(
    ! [C_44] :
      ( C_44 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_44) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_44,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_485])).

tff(c_688,plain,(
    ! [C_44] :
      ( C_44 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_44) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(C_44,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_486])).

tff(c_691,plain,
    ( '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_688])).

tff(c_692,plain,(
    ~ r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_274,c_691])).

tff(c_779,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_776,c_692])).

tff(c_787,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_62,c_779])).

tff(c_788,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_787])).

tff(c_796,plain,
    ( ~ v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_788])).

tff(c_803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_185,c_796])).

tff(c_804,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_805,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_864,plain,(
    ! [C_158,A_159,B_160] :
      ( v1_relat_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_877,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_864])).

tff(c_30,plain,(
    ! [A_12,B_15] :
      ( k1_funct_1(A_12,B_15) = k1_xboole_0
      | r2_hidden(B_15,k1_relat_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_884,plain,(
    ! [A_162,B_163] :
      ( ~ r2_hidden('#skF_1'(A_162,B_163),B_163)
      | r1_tarski(A_162,B_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_889,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_884])).

tff(c_66,plain,
    ( k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_854,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_805,c_66])).

tff(c_1363,plain,(
    ! [B_236,A_237] :
      ( r2_hidden(k4_tarski(B_236,k1_funct_1(A_237,B_236)),A_237)
      | ~ r2_hidden(B_236,k1_relat_1(A_237))
      | ~ v1_funct_1(A_237)
      | ~ v1_relat_1(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1380,plain,
    ( r2_hidden(k4_tarski('#skF_7',k1_funct_1('#skF_5','#skF_6')),'#skF_5')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_854,c_1363])).

tff(c_1386,plain,
    ( r2_hidden(k4_tarski('#skF_7',k1_funct_1('#skF_5','#skF_6')),'#skF_5')
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_62,c_1380])).

tff(c_1394,plain,(
    ~ r2_hidden('#skF_7',k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1386])).

tff(c_1397,plain,
    ( k1_funct_1('#skF_5','#skF_7') = k1_xboole_0
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_1394])).

tff(c_1403,plain,(
    k1_funct_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_62,c_854,c_1397])).

tff(c_1405,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1403,c_854])).

tff(c_68,plain,
    ( r2_hidden('#skF_7','#skF_4')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_817,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_805,c_68])).

tff(c_1756,plain,(
    ! [D_278,C_279,B_280,A_281] :
      ( k1_funct_1(k2_funct_1(D_278),k1_funct_1(D_278,C_279)) = C_279
      | k1_xboole_0 = B_280
      | ~ r2_hidden(C_279,A_281)
      | ~ v2_funct_1(D_278)
      | ~ m1_subset_1(D_278,k1_zfmisc_1(k2_zfmisc_1(A_281,B_280)))
      | ~ v1_funct_2(D_278,A_281,B_280)
      | ~ v1_funct_1(D_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1885,plain,(
    ! [D_288,B_289] :
      ( k1_funct_1(k2_funct_1(D_288),k1_funct_1(D_288,'#skF_7')) = '#skF_7'
      | k1_xboole_0 = B_289
      | ~ v2_funct_1(D_288)
      | ~ m1_subset_1(D_288,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_289)))
      | ~ v1_funct_2(D_288,'#skF_4',B_289)
      | ~ v1_funct_1(D_288) ) ),
    inference(resolution,[status(thm)],[c_817,c_1756])).

tff(c_1890,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_1885])).

tff(c_1897,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_xboole_0) = '#skF_7'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_805,c_1405,c_1890])).

tff(c_1899,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1897])).

tff(c_12,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_813,plain,(
    ! [A_149,B_150] : v1_relat_1(k2_zfmisc_1(A_149,B_150)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_815,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_813])).

tff(c_54,plain,(
    ! [A_34,B_35] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_944,plain,(
    ! [A_34] : v4_relat_1(k1_xboole_0,A_34) ),
    inference(resolution,[status(thm)],[c_54,c_931])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_983,plain,(
    ! [B_188,A_189] :
      ( r1_tarski(k1_relat_1(B_188),A_189)
      | ~ v4_relat_1(B_188,A_189)
      | ~ v1_relat_1(B_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_993,plain,(
    ! [A_189] :
      ( r1_tarski(k1_xboole_0,A_189)
      | ~ v4_relat_1(k1_xboole_0,A_189)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_983])).

tff(c_998,plain,(
    ! [A_190] : r1_tarski(k1_xboole_0,A_190) ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_944,c_993])).

tff(c_70,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_837,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_805,c_70])).

tff(c_952,plain,(
    ! [C_182,B_183,A_184] :
      ( r2_hidden(C_182,B_183)
      | ~ r2_hidden(C_182,A_184)
      | ~ r1_tarski(A_184,B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_962,plain,(
    ! [B_185] :
      ( r2_hidden('#skF_6',B_185)
      | ~ r1_tarski('#skF_4',B_185) ) ),
    inference(resolution,[status(thm)],[c_837,c_952])).

tff(c_46,plain,(
    ! [B_27,A_26] :
      ( ~ r1_tarski(B_27,A_26)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_969,plain,(
    ! [B_185] :
      ( ~ r1_tarski(B_185,'#skF_6')
      | ~ r1_tarski('#skF_4',B_185) ) ),
    inference(resolution,[status(thm)],[c_962,c_46])).

tff(c_1006,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_998,c_969])).

tff(c_1926,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1899,c_1006])).

tff(c_1943,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_1926])).

tff(c_1945,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1897])).

tff(c_1944,plain,(
    k1_funct_1(k2_funct_1('#skF_5'),k1_xboole_0) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1897])).

tff(c_2097,plain,(
    ! [D_302,B_303] :
      ( k1_funct_1(k2_funct_1(D_302),k1_funct_1(D_302,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_303
      | ~ v2_funct_1(D_302)
      | ~ m1_subset_1(D_302,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_303)))
      | ~ v1_funct_2(D_302,'#skF_4',B_303)
      | ~ v1_funct_1(D_302) ) ),
    inference(resolution,[status(thm)],[c_837,c_1756])).

tff(c_2102,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_2097])).

tff(c_2109,plain,
    ( '#skF_7' = '#skF_6'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_805,c_1944,c_1403,c_2102])).

tff(c_2111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1945,c_804,c_2109])).

tff(c_2113,plain,(
    r2_hidden('#skF_7',k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1386])).

tff(c_2140,plain,(
    ! [B_304,A_305] :
      ( k1_funct_1(k2_funct_1(B_304),k1_funct_1(B_304,A_305)) = A_305
      | ~ r2_hidden(A_305,k1_relat_1(B_304))
      | ~ v2_funct_1(B_304)
      | ~ v1_funct_1(B_304)
      | ~ v1_relat_1(B_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2167,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_7'
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_854,c_2140])).

tff(c_2173,plain,(
    k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_62,c_805,c_2113,c_2167])).

tff(c_44,plain,(
    ! [B_25,A_24] :
      ( k1_funct_1(k2_funct_1(B_25),k1_funct_1(B_25,A_24)) = A_24
      | ~ r2_hidden(A_24,k1_relat_1(B_25))
      | ~ v2_funct_1(B_25)
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2180,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2173,c_44])).

tff(c_2190,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_62,c_805,c_2180])).

tff(c_2191,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_804,c_2190])).

tff(c_2198,plain,
    ( k1_funct_1('#skF_5','#skF_6') = k1_xboole_0
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_2191])).

tff(c_2204,plain,(
    k1_funct_1('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_62,c_2198])).

tff(c_2206,plain,(
    k1_funct_1(k2_funct_1('#skF_5'),k1_xboole_0) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2204,c_2173])).

tff(c_2639,plain,(
    ! [D_344,C_345,B_346,A_347] :
      ( k1_funct_1(k2_funct_1(D_344),k1_funct_1(D_344,C_345)) = C_345
      | k1_xboole_0 = B_346
      | ~ r2_hidden(C_345,A_347)
      | ~ v2_funct_1(D_344)
      | ~ m1_subset_1(D_344,k1_zfmisc_1(k2_zfmisc_1(A_347,B_346)))
      | ~ v1_funct_2(D_344,A_347,B_346)
      | ~ v1_funct_1(D_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2971,plain,(
    ! [D_370,B_371] :
      ( k1_funct_1(k2_funct_1(D_370),k1_funct_1(D_370,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_371
      | ~ v2_funct_1(D_370)
      | ~ m1_subset_1(D_370,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_371)))
      | ~ v1_funct_2(D_370,'#skF_4',B_371)
      | ~ v1_funct_1(D_370) ) ),
    inference(resolution,[status(thm)],[c_837,c_2639])).

tff(c_2976,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_2971])).

tff(c_2983,plain,
    ( '#skF_7' = '#skF_6'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_805,c_2206,c_2204,c_2976])).

tff(c_2984,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_804,c_2983])).

tff(c_997,plain,(
    ! [A_189] : r1_tarski(k1_xboole_0,A_189) ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_944,c_993])).

tff(c_1161,plain,(
    ! [A_210,B_211,B_212] :
      ( r2_hidden('#skF_1'(A_210,B_211),B_212)
      | ~ r1_tarski(A_210,B_212)
      | r1_tarski(A_210,B_211) ) ),
    inference(resolution,[status(thm)],[c_6,c_952])).

tff(c_1174,plain,(
    ! [B_213,A_214,B_215] :
      ( ~ r1_tarski(B_213,'#skF_1'(A_214,B_215))
      | ~ r1_tarski(A_214,B_213)
      | r1_tarski(A_214,B_215) ) ),
    inference(resolution,[status(thm)],[c_1161,c_46])).

tff(c_1191,plain,(
    ! [A_216,B_217] :
      ( ~ r1_tarski(A_216,k1_xboole_0)
      | r1_tarski(A_216,B_217) ) ),
    inference(resolution,[status(thm)],[c_997,c_1174])).

tff(c_1203,plain,(
    ! [B_9,B_217] :
      ( r1_tarski(k1_relat_1(B_9),B_217)
      | ~ v4_relat_1(B_9,k1_xboole_0)
      | ~ v1_relat_1(B_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_1191])).

tff(c_2120,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_2113,c_46])).

tff(c_2123,plain,
    ( ~ v4_relat_1('#skF_5',k1_xboole_0)
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1203,c_2120])).

tff(c_2129,plain,(
    ~ v4_relat_1('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_877,c_2123])).

tff(c_3011,plain,(
    ~ v4_relat_1('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2984,c_2129])).

tff(c_3041,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_945,c_3011])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n009.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 15:12:41 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.95/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.95/1.88  
% 4.95/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.95/1.88  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 4.95/1.88  
% 4.95/1.88  %Foreground sorts:
% 4.95/1.88  
% 4.95/1.88  
% 4.95/1.88  %Background operators:
% 4.95/1.88  
% 4.95/1.88  
% 4.95/1.88  %Foreground operators:
% 4.95/1.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.95/1.88  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.95/1.88  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.95/1.88  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.95/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.95/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.95/1.88  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.95/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.95/1.88  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.95/1.88  tff('#skF_7', type, '#skF_7': $i).
% 4.95/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.95/1.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.95/1.88  tff('#skF_5', type, '#skF_5': $i).
% 4.95/1.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.95/1.88  tff('#skF_6', type, '#skF_6': $i).
% 4.95/1.88  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.95/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.95/1.88  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.95/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.95/1.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.95/1.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.95/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.95/1.88  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.95/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.95/1.88  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.95/1.88  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.95/1.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.95/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.95/1.88  
% 4.95/1.90  tff(f_143, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 4.95/1.90  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.95/1.90  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.95/1.90  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.95/1.90  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 4.95/1.90  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.95/1.90  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 4.95/1.90  tff(f_125, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 4.95/1.90  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.95/1.90  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.95/1.90  tff(f_111, axiom, (![A, B]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relset_1)).
% 4.95/1.90  tff(f_49, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.95/1.90  tff(f_99, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.95/1.90  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_funct_1)).
% 4.95/1.90  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.95/1.90  tff(c_931, plain, (![C_176, A_177, B_178]: (v4_relat_1(C_176, A_177) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.95/1.90  tff(c_945, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_931])).
% 4.95/1.90  tff(c_126, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.95/1.90  tff(c_139, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_126])).
% 4.95/1.90  tff(c_171, plain, (![C_67, A_68, B_69]: (v4_relat_1(C_67, A_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.95/1.90  tff(c_185, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_171])).
% 4.95/1.90  tff(c_16, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(B_9), A_8) | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.95/1.90  tff(c_64, plain, ('#skF_7'!='#skF_6' | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.95/1.90  tff(c_91, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_64])).
% 4.95/1.90  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.95/1.90  tff(c_289, plain, (![A_93]: (r2_hidden('#skF_3'(A_93), k1_relat_1(A_93)) | v2_funct_1(A_93) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.95/1.90  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.95/1.90  tff(c_776, plain, (![A_146, B_147]: (r2_hidden('#skF_3'(A_146), B_147) | ~r1_tarski(k1_relat_1(A_146), B_147) | v2_funct_1(A_146) | ~v1_funct_1(A_146) | ~v1_relat_1(A_146))), inference(resolution, [status(thm)], [c_289, c_2])).
% 4.95/1.90  tff(c_268, plain, (![A_91]: ('#skF_2'(A_91)!='#skF_3'(A_91) | v2_funct_1(A_91) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.95/1.90  tff(c_271, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_268, c_91])).
% 4.95/1.90  tff(c_274, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_62, c_271])).
% 4.95/1.90  tff(c_275, plain, (![A_92]: (r2_hidden('#skF_2'(A_92), k1_relat_1(A_92)) | v2_funct_1(A_92) | ~v1_funct_1(A_92) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.95/1.90  tff(c_610, plain, (![A_128, B_129]: (r2_hidden('#skF_2'(A_128), B_129) | ~r1_tarski(k1_relat_1(A_128), B_129) | v2_funct_1(A_128) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128))), inference(resolution, [status(thm)], [c_275, c_2])).
% 4.95/1.90  tff(c_470, plain, (![A_115]: (k1_funct_1(A_115, '#skF_2'(A_115))=k1_funct_1(A_115, '#skF_3'(A_115)) | v2_funct_1(A_115) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.95/1.90  tff(c_82, plain, (![D_45, C_44]: (v2_funct_1('#skF_5') | D_45=C_44 | k1_funct_1('#skF_5', D_45)!=k1_funct_1('#skF_5', C_44) | ~r2_hidden(D_45, '#skF_4') | ~r2_hidden(C_44, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.95/1.90  tff(c_187, plain, (![D_45, C_44]: (D_45=C_44 | k1_funct_1('#skF_5', D_45)!=k1_funct_1('#skF_5', C_44) | ~r2_hidden(D_45, '#skF_4') | ~r2_hidden(C_44, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_91, c_82])).
% 4.95/1.90  tff(c_479, plain, (![D_45]: (D_45='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_45)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_45, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_470, c_187])).
% 4.95/1.90  tff(c_488, plain, (![D_45]: (D_45='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_45)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_45, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_62, c_479])).
% 4.95/1.90  tff(c_489, plain, (![D_45]: (D_45='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_45)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_45, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_91, c_488])).
% 4.95/1.90  tff(c_609, plain, (~r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_489])).
% 4.95/1.90  tff(c_613, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_610, c_609])).
% 4.95/1.90  tff(c_621, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_62, c_613])).
% 4.95/1.90  tff(c_622, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_91, c_621])).
% 4.95/1.90  tff(c_630, plain, (~v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_622])).
% 4.95/1.90  tff(c_637, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_185, c_630])).
% 4.95/1.90  tff(c_639, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_489])).
% 4.95/1.90  tff(c_476, plain, (![C_44]: (C_44='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_44)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_44, '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_470, c_187])).
% 4.95/1.90  tff(c_485, plain, (![C_44]: (C_44='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_44)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_44, '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_62, c_476])).
% 4.95/1.90  tff(c_486, plain, (![C_44]: (C_44='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_44)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_44, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_91, c_485])).
% 4.95/1.90  tff(c_688, plain, (![C_44]: (C_44='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_44)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(C_44, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_639, c_486])).
% 4.95/1.90  tff(c_691, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_688])).
% 4.95/1.90  tff(c_692, plain, (~r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_274, c_691])).
% 4.95/1.90  tff(c_779, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_776, c_692])).
% 4.95/1.90  tff(c_787, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_62, c_779])).
% 4.95/1.90  tff(c_788, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_91, c_787])).
% 4.95/1.90  tff(c_796, plain, (~v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_788])).
% 4.95/1.90  tff(c_803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_185, c_796])).
% 4.95/1.90  tff(c_804, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_64])).
% 4.95/1.90  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.95/1.90  tff(c_805, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_64])).
% 4.95/1.90  tff(c_864, plain, (![C_158, A_159, B_160]: (v1_relat_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.95/1.90  tff(c_877, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_864])).
% 4.95/1.90  tff(c_30, plain, (![A_12, B_15]: (k1_funct_1(A_12, B_15)=k1_xboole_0 | r2_hidden(B_15, k1_relat_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.95/1.90  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.95/1.90  tff(c_884, plain, (![A_162, B_163]: (~r2_hidden('#skF_1'(A_162, B_163), B_163) | r1_tarski(A_162, B_163))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.95/1.90  tff(c_889, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_884])).
% 4.95/1.90  tff(c_66, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.95/1.90  tff(c_854, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_805, c_66])).
% 4.95/1.90  tff(c_1363, plain, (![B_236, A_237]: (r2_hidden(k4_tarski(B_236, k1_funct_1(A_237, B_236)), A_237) | ~r2_hidden(B_236, k1_relat_1(A_237)) | ~v1_funct_1(A_237) | ~v1_relat_1(A_237))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.95/1.90  tff(c_1380, plain, (r2_hidden(k4_tarski('#skF_7', k1_funct_1('#skF_5', '#skF_6')), '#skF_5') | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_854, c_1363])).
% 4.95/1.90  tff(c_1386, plain, (r2_hidden(k4_tarski('#skF_7', k1_funct_1('#skF_5', '#skF_6')), '#skF_5') | ~r2_hidden('#skF_7', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_877, c_62, c_1380])).
% 4.95/1.90  tff(c_1394, plain, (~r2_hidden('#skF_7', k1_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_1386])).
% 4.95/1.90  tff(c_1397, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_xboole_0 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_1394])).
% 4.95/1.90  tff(c_1403, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_877, c_62, c_854, c_1397])).
% 4.95/1.90  tff(c_1405, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1403, c_854])).
% 4.95/1.90  tff(c_68, plain, (r2_hidden('#skF_7', '#skF_4') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.95/1.90  tff(c_817, plain, (r2_hidden('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_805, c_68])).
% 4.95/1.90  tff(c_1756, plain, (![D_278, C_279, B_280, A_281]: (k1_funct_1(k2_funct_1(D_278), k1_funct_1(D_278, C_279))=C_279 | k1_xboole_0=B_280 | ~r2_hidden(C_279, A_281) | ~v2_funct_1(D_278) | ~m1_subset_1(D_278, k1_zfmisc_1(k2_zfmisc_1(A_281, B_280))) | ~v1_funct_2(D_278, A_281, B_280) | ~v1_funct_1(D_278))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.95/1.90  tff(c_1885, plain, (![D_288, B_289]: (k1_funct_1(k2_funct_1(D_288), k1_funct_1(D_288, '#skF_7'))='#skF_7' | k1_xboole_0=B_289 | ~v2_funct_1(D_288) | ~m1_subset_1(D_288, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_289))) | ~v1_funct_2(D_288, '#skF_4', B_289) | ~v1_funct_1(D_288))), inference(resolution, [status(thm)], [c_817, c_1756])).
% 4.95/1.90  tff(c_1890, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_7'))='#skF_7' | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_1885])).
% 4.95/1.90  tff(c_1897, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_xboole_0)='#skF_7' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_805, c_1405, c_1890])).
% 4.95/1.90  tff(c_1899, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1897])).
% 4.95/1.90  tff(c_12, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.95/1.90  tff(c_813, plain, (![A_149, B_150]: (v1_relat_1(k2_zfmisc_1(A_149, B_150)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.95/1.90  tff(c_815, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_813])).
% 4.95/1.90  tff(c_54, plain, (![A_34, B_35]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.95/1.90  tff(c_944, plain, (![A_34]: (v4_relat_1(k1_xboole_0, A_34))), inference(resolution, [status(thm)], [c_54, c_931])).
% 4.95/1.90  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.95/1.90  tff(c_983, plain, (![B_188, A_189]: (r1_tarski(k1_relat_1(B_188), A_189) | ~v4_relat_1(B_188, A_189) | ~v1_relat_1(B_188))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.95/1.90  tff(c_993, plain, (![A_189]: (r1_tarski(k1_xboole_0, A_189) | ~v4_relat_1(k1_xboole_0, A_189) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_983])).
% 4.95/1.90  tff(c_998, plain, (![A_190]: (r1_tarski(k1_xboole_0, A_190))), inference(demodulation, [status(thm), theory('equality')], [c_815, c_944, c_993])).
% 4.95/1.90  tff(c_70, plain, (r2_hidden('#skF_6', '#skF_4') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.95/1.90  tff(c_837, plain, (r2_hidden('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_805, c_70])).
% 4.95/1.90  tff(c_952, plain, (![C_182, B_183, A_184]: (r2_hidden(C_182, B_183) | ~r2_hidden(C_182, A_184) | ~r1_tarski(A_184, B_183))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.95/1.90  tff(c_962, plain, (![B_185]: (r2_hidden('#skF_6', B_185) | ~r1_tarski('#skF_4', B_185))), inference(resolution, [status(thm)], [c_837, c_952])).
% 4.95/1.90  tff(c_46, plain, (![B_27, A_26]: (~r1_tarski(B_27, A_26) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.95/1.90  tff(c_969, plain, (![B_185]: (~r1_tarski(B_185, '#skF_6') | ~r1_tarski('#skF_4', B_185))), inference(resolution, [status(thm)], [c_962, c_46])).
% 4.95/1.90  tff(c_1006, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_998, c_969])).
% 4.95/1.90  tff(c_1926, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1899, c_1006])).
% 4.95/1.90  tff(c_1943, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_889, c_1926])).
% 4.95/1.90  tff(c_1945, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_1897])).
% 4.95/1.90  tff(c_1944, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_xboole_0)='#skF_7'), inference(splitRight, [status(thm)], [c_1897])).
% 4.95/1.90  tff(c_2097, plain, (![D_302, B_303]: (k1_funct_1(k2_funct_1(D_302), k1_funct_1(D_302, '#skF_6'))='#skF_6' | k1_xboole_0=B_303 | ~v2_funct_1(D_302) | ~m1_subset_1(D_302, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_303))) | ~v1_funct_2(D_302, '#skF_4', B_303) | ~v1_funct_1(D_302))), inference(resolution, [status(thm)], [c_837, c_1756])).
% 4.95/1.90  tff(c_2102, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_2097])).
% 4.95/1.90  tff(c_2109, plain, ('#skF_7'='#skF_6' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_805, c_1944, c_1403, c_2102])).
% 4.95/1.90  tff(c_2111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1945, c_804, c_2109])).
% 4.95/1.90  tff(c_2113, plain, (r2_hidden('#skF_7', k1_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_1386])).
% 4.95/1.90  tff(c_2140, plain, (![B_304, A_305]: (k1_funct_1(k2_funct_1(B_304), k1_funct_1(B_304, A_305))=A_305 | ~r2_hidden(A_305, k1_relat_1(B_304)) | ~v2_funct_1(B_304) | ~v1_funct_1(B_304) | ~v1_relat_1(B_304))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.95/1.90  tff(c_2167, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_7' | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_854, c_2140])).
% 4.95/1.90  tff(c_2173, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_877, c_62, c_805, c_2113, c_2167])).
% 4.95/1.90  tff(c_44, plain, (![B_25, A_24]: (k1_funct_1(k2_funct_1(B_25), k1_funct_1(B_25, A_24))=A_24 | ~r2_hidden(A_24, k1_relat_1(B_25)) | ~v2_funct_1(B_25) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.95/1.90  tff(c_2180, plain, ('#skF_7'='#skF_6' | ~r2_hidden('#skF_6', k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2173, c_44])).
% 4.95/1.90  tff(c_2190, plain, ('#skF_7'='#skF_6' | ~r2_hidden('#skF_6', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_877, c_62, c_805, c_2180])).
% 4.95/1.90  tff(c_2191, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_804, c_2190])).
% 4.95/1.90  tff(c_2198, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_xboole_0 | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_2191])).
% 4.95/1.90  tff(c_2204, plain, (k1_funct_1('#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_877, c_62, c_2198])).
% 4.95/1.90  tff(c_2206, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_xboole_0)='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2204, c_2173])).
% 4.95/1.90  tff(c_2639, plain, (![D_344, C_345, B_346, A_347]: (k1_funct_1(k2_funct_1(D_344), k1_funct_1(D_344, C_345))=C_345 | k1_xboole_0=B_346 | ~r2_hidden(C_345, A_347) | ~v2_funct_1(D_344) | ~m1_subset_1(D_344, k1_zfmisc_1(k2_zfmisc_1(A_347, B_346))) | ~v1_funct_2(D_344, A_347, B_346) | ~v1_funct_1(D_344))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.95/1.90  tff(c_2971, plain, (![D_370, B_371]: (k1_funct_1(k2_funct_1(D_370), k1_funct_1(D_370, '#skF_6'))='#skF_6' | k1_xboole_0=B_371 | ~v2_funct_1(D_370) | ~m1_subset_1(D_370, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_371))) | ~v1_funct_2(D_370, '#skF_4', B_371) | ~v1_funct_1(D_370))), inference(resolution, [status(thm)], [c_837, c_2639])).
% 4.95/1.90  tff(c_2976, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_2971])).
% 4.95/1.90  tff(c_2983, plain, ('#skF_7'='#skF_6' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_805, c_2206, c_2204, c_2976])).
% 4.95/1.90  tff(c_2984, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_804, c_2983])).
% 4.95/1.90  tff(c_997, plain, (![A_189]: (r1_tarski(k1_xboole_0, A_189))), inference(demodulation, [status(thm), theory('equality')], [c_815, c_944, c_993])).
% 4.95/1.90  tff(c_1161, plain, (![A_210, B_211, B_212]: (r2_hidden('#skF_1'(A_210, B_211), B_212) | ~r1_tarski(A_210, B_212) | r1_tarski(A_210, B_211))), inference(resolution, [status(thm)], [c_6, c_952])).
% 4.95/1.90  tff(c_1174, plain, (![B_213, A_214, B_215]: (~r1_tarski(B_213, '#skF_1'(A_214, B_215)) | ~r1_tarski(A_214, B_213) | r1_tarski(A_214, B_215))), inference(resolution, [status(thm)], [c_1161, c_46])).
% 4.95/1.90  tff(c_1191, plain, (![A_216, B_217]: (~r1_tarski(A_216, k1_xboole_0) | r1_tarski(A_216, B_217))), inference(resolution, [status(thm)], [c_997, c_1174])).
% 4.95/1.90  tff(c_1203, plain, (![B_9, B_217]: (r1_tarski(k1_relat_1(B_9), B_217) | ~v4_relat_1(B_9, k1_xboole_0) | ~v1_relat_1(B_9))), inference(resolution, [status(thm)], [c_16, c_1191])).
% 4.95/1.90  tff(c_2120, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_7')), inference(resolution, [status(thm)], [c_2113, c_46])).
% 4.95/1.90  tff(c_2123, plain, (~v4_relat_1('#skF_5', k1_xboole_0) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1203, c_2120])).
% 4.95/1.90  tff(c_2129, plain, (~v4_relat_1('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_877, c_2123])).
% 4.95/1.90  tff(c_3011, plain, (~v4_relat_1('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2984, c_2129])).
% 4.95/1.90  tff(c_3041, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_945, c_3011])).
% 4.95/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.95/1.90  
% 4.95/1.90  Inference rules
% 4.95/1.90  ----------------------
% 4.95/1.90  #Ref     : 4
% 4.95/1.90  #Sup     : 647
% 4.95/1.90  #Fact    : 0
% 4.95/1.90  #Define  : 0
% 4.95/1.90  #Split   : 13
% 4.95/1.90  #Chain   : 0
% 4.95/1.90  #Close   : 0
% 4.95/1.90  
% 4.95/1.90  Ordering : KBO
% 4.95/1.90  
% 4.95/1.90  Simplification rules
% 4.95/1.90  ----------------------
% 4.95/1.90  #Subsume      : 193
% 4.95/1.90  #Demod        : 525
% 4.95/1.90  #Tautology    : 147
% 4.95/1.90  #SimpNegUnit  : 12
% 4.95/1.90  #BackRed      : 98
% 4.95/1.90  
% 4.95/1.90  #Partial instantiations: 0
% 4.95/1.90  #Strategies tried      : 1
% 4.95/1.90  
% 4.95/1.90  Timing (in seconds)
% 4.95/1.90  ----------------------
% 4.95/1.91  Preprocessing        : 0.34
% 4.95/1.91  Parsing              : 0.18
% 4.95/1.91  CNF conversion       : 0.02
% 4.95/1.91  Main loop            : 0.79
% 4.95/1.91  Inferencing          : 0.26
% 4.95/1.91  Reduction            : 0.27
% 4.95/1.91  Demodulation         : 0.18
% 4.95/1.91  BG Simplification    : 0.04
% 4.95/1.91  Subsumption          : 0.16
% 4.95/1.91  Abstraction          : 0.03
% 4.95/1.91  MUC search           : 0.00
% 4.95/1.91  Cooper               : 0.00
% 4.95/1.91  Total                : 1.19
% 4.95/1.91  Index Insertion      : 0.00
% 4.95/1.91  Index Deletion       : 0.00
% 4.95/1.91  Index Matching       : 0.00
% 4.95/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
