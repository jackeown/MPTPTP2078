%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:42 EST 2020

% Result     : Theorem 5.32s
% Output     : CNFRefutation 5.32s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 329 expanded)
%              Number of leaves         :   51 ( 131 expanded)
%              Depth                    :   14
%              Number of atoms          :  172 ( 667 expanded)
%              Number of equality atoms :   52 ( 166 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_97,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_174,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_119,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_137,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_141,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(f_162,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_50,plain,(
    ! [A_37,B_38] : v1_relat_1(k2_zfmisc_1(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_80,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_240,plain,(
    ! [B_102,A_103] :
      ( v1_relat_1(B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_103))
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_246,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_80,c_240])).

tff(c_250,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_246])).

tff(c_52,plain,(
    ! [B_40,A_39] :
      ( r1_tarski(k9_relat_1(B_40,A_39),k2_relat_1(B_40))
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_60,plain,(
    ! [A_45] :
      ( k1_relat_1(A_45) != k1_xboole_0
      | k1_xboole_0 = A_45
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_258,plain,
    ( k1_relat_1('#skF_7') != k1_xboole_0
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_250,c_60])).

tff(c_260,plain,(
    k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_258])).

tff(c_84,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_925,plain,(
    ! [B_206,A_207] :
      ( k1_tarski(k1_funct_1(B_206,A_207)) = k2_relat_1(B_206)
      | k1_tarski(A_207) != k1_relat_1(B_206)
      | ~ v1_funct_1(B_206)
      | ~ v1_relat_1(B_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_76,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_7','#skF_6'),k1_tarski(k1_funct_1('#skF_7','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_936,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_7','#skF_6'),k2_relat_1('#skF_7'))
    | k1_tarski('#skF_4') != k1_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_925,c_76])).

tff(c_944,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_7','#skF_6'),k2_relat_1('#skF_7'))
    | k1_tarski('#skF_4') != k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_84,c_936])).

tff(c_1002,plain,(
    k1_tarski('#skF_4') != k1_relat_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_944])).

tff(c_586,plain,(
    ! [C_166,A_167,B_168] :
      ( v4_relat_1(C_166,A_167)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_595,plain,(
    v4_relat_1('#skF_7',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_586])).

tff(c_349,plain,(
    ! [B_119,A_120] :
      ( r1_tarski(k1_relat_1(B_119),A_120)
      | ~ v4_relat_1(B_119,A_120)
      | ~ v1_relat_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    ! [B_21,A_20] :
      ( k1_tarski(B_21) = A_20
      | k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,k1_tarski(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2378,plain,(
    ! [B_300,B_301] :
      ( k1_tarski(B_300) = k1_relat_1(B_301)
      | k1_relat_1(B_301) = k1_xboole_0
      | ~ v4_relat_1(B_301,k1_tarski(B_300))
      | ~ v1_relat_1(B_301) ) ),
    inference(resolution,[status(thm)],[c_349,c_22])).

tff(c_2416,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_7')
    | k1_relat_1('#skF_7') = k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_595,c_2378])).

tff(c_2433,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_7')
    | k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_2416])).

tff(c_2435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_1002,c_2433])).

tff(c_2437,plain,(
    k1_tarski('#skF_4') = k1_relat_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_944])).

tff(c_2445,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_7'),'#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_80])).

tff(c_2535,plain,(
    ! [A_302,B_303,C_304,D_305] :
      ( k7_relset_1(A_302,B_303,C_304,D_305) = k9_relat_1(C_304,D_305)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(k2_zfmisc_1(A_302,B_303))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2541,plain,(
    ! [D_305] : k7_relset_1(k1_relat_1('#skF_7'),'#skF_5','#skF_7',D_305) = k9_relat_1('#skF_7',D_305) ),
    inference(resolution,[status(thm)],[c_2445,c_2535])).

tff(c_2436,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_7','#skF_6'),k2_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_944])).

tff(c_2530,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_7'),'#skF_5','#skF_7','#skF_6'),k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2437,c_2436])).

tff(c_2569,plain,(
    ~ r1_tarski(k9_relat_1('#skF_7','#skF_6'),k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2541,c_2530])).

tff(c_2602,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_2569])).

tff(c_2609,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_2602])).

tff(c_2610,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_258])).

tff(c_58,plain,(
    ! [A_45] :
      ( k2_relat_1(A_45) != k1_xboole_0
      | k1_xboole_0 = A_45
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_257,plain,
    ( k2_relat_1('#skF_7') != k1_xboole_0
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_250,c_58])).

tff(c_259,plain,(
    k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_2612,plain,(
    k2_relat_1('#skF_7') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2610,c_259])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,(
    ! [A_33] :
      ( v1_xboole_0(k2_relat_1(A_33))
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_114,plain,(
    ! [A_89] :
      ( r2_hidden('#skF_3'(A_89),A_89)
      | k1_xboole_0 = A_89 ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [A_92] :
      ( ~ v1_xboole_0(A_92)
      | k1_xboole_0 = A_92 ) ),
    inference(resolution,[status(thm)],[c_114,c_2])).

tff(c_138,plain,(
    ! [A_93] :
      ( k2_relat_1(A_93) = k1_xboole_0
      | ~ v1_xboole_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_42,c_128])).

tff(c_146,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_138])).

tff(c_2616,plain,(
    k2_relat_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2610,c_2610,c_146])).

tff(c_2653,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2612,c_2616])).

tff(c_2654,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_2665,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2654,c_12])).

tff(c_2655,plain,(
    k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_2677,plain,(
    k2_relat_1('#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2654,c_2655])).

tff(c_2760,plain,(
    ! [B_319,A_320] :
      ( r1_tarski(k9_relat_1(B_319,A_320),k2_relat_1(B_319))
      | ~ v1_relat_1(B_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2766,plain,(
    ! [A_320] :
      ( r1_tarski(k9_relat_1('#skF_7',A_320),'#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2677,c_2760])).

tff(c_2768,plain,(
    ! [A_320] : r1_tarski(k9_relat_1('#skF_7',A_320),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_2766])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2937,plain,(
    ! [C_347,B_348,A_349] :
      ( ~ v1_xboole_0(C_347)
      | ~ m1_subset_1(B_348,k1_zfmisc_1(C_347))
      | ~ r2_hidden(A_349,B_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2960,plain,(
    ! [B_353,A_354,A_355] :
      ( ~ v1_xboole_0(B_353)
      | ~ r2_hidden(A_354,A_355)
      | ~ r1_tarski(A_355,B_353) ) ),
    inference(resolution,[status(thm)],[c_30,c_2937])).

tff(c_2970,plain,(
    ! [B_356,A_357] :
      ( ~ v1_xboole_0(B_356)
      | ~ r1_tarski(A_357,B_356)
      | v1_xboole_0(A_357) ) ),
    inference(resolution,[status(thm)],[c_4,c_2960])).

tff(c_2979,plain,(
    ! [A_320] :
      ( ~ v1_xboole_0('#skF_7')
      | v1_xboole_0(k9_relat_1('#skF_7',A_320)) ) ),
    inference(resolution,[status(thm)],[c_2768,c_2970])).

tff(c_3004,plain,(
    ! [A_358] : v1_xboole_0(k9_relat_1('#skF_7',A_358)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2665,c_2979])).

tff(c_118,plain,(
    ! [A_89] :
      ( ~ v1_xboole_0(A_89)
      | k1_xboole_0 = A_89 ) ),
    inference(resolution,[status(thm)],[c_114,c_2])).

tff(c_2661,plain,(
    ! [A_89] :
      ( ~ v1_xboole_0(A_89)
      | A_89 = '#skF_7' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2654,c_118])).

tff(c_3015,plain,(
    ! [A_358] : k9_relat_1('#skF_7',A_358) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3004,c_2661])).

tff(c_3661,plain,(
    ! [A_448,B_449,C_450,D_451] :
      ( k7_relset_1(A_448,B_449,C_450,D_451) = k9_relat_1(C_450,D_451)
      | ~ m1_subset_1(C_450,k1_zfmisc_1(k2_zfmisc_1(A_448,B_449))) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_3666,plain,(
    ! [D_451] : k7_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_7',D_451) = k9_relat_1('#skF_7',D_451) ),
    inference(resolution,[status(thm)],[c_80,c_3661])).

tff(c_3669,plain,(
    ! [D_451] : k7_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_7',D_451) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3015,c_3666])).

tff(c_2692,plain,(
    ! [A_310,B_311] :
      ( r2_hidden('#skF_2'(A_310,B_311),A_310)
      | r1_tarski(A_310,B_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2710,plain,(
    ! [A_314,B_315] :
      ( ~ v1_xboole_0(A_314)
      | r1_tarski(A_314,B_315) ) ),
    inference(resolution,[status(thm)],[c_2692,c_2])).

tff(c_2714,plain,(
    ~ v1_xboole_0(k7_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_2710,c_76])).

tff(c_3670,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3669,c_2714])).

tff(c_3674,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2665,c_3670])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.32/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.32/2.00  
% 5.32/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.32/2.00  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_enumset1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2
% 5.32/2.00  
% 5.32/2.00  %Foreground sorts:
% 5.32/2.00  
% 5.32/2.00  
% 5.32/2.00  %Background operators:
% 5.32/2.00  
% 5.32/2.00  
% 5.32/2.00  %Foreground operators:
% 5.32/2.00  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.32/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.32/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.32/2.00  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.32/2.00  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.32/2.00  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.32/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.32/2.00  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.32/2.00  tff('#skF_7', type, '#skF_7': $i).
% 5.32/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.32/2.00  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.32/2.00  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.32/2.00  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.32/2.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.32/2.00  tff('#skF_5', type, '#skF_5': $i).
% 5.32/2.00  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.32/2.00  tff('#skF_6', type, '#skF_6': $i).
% 5.32/2.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.32/2.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.32/2.00  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.32/2.00  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.32/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.32/2.00  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.32/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.32/2.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.32/2.00  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.32/2.00  tff('#skF_4', type, '#skF_4': $i).
% 5.32/2.00  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.32/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.32/2.00  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.32/2.00  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.32/2.00  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.32/2.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.32/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.32/2.00  
% 5.32/2.02  tff(f_97, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.32/2.02  tff(f_174, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 5.32/2.02  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.32/2.02  tff(f_101, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 5.32/2.02  tff(f_119, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 5.32/2.02  tff(f_131, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 5.32/2.02  tff(f_137, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.32/2.02  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 5.32/2.02  tff(f_53, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 5.32/2.02  tff(f_141, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.32/2.02  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.32/2.02  tff(f_85, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 5.32/2.02  tff(f_162, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_mcart_1)).
% 5.32/2.02  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.32/2.02  tff(f_57, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.32/2.02  tff(f_64, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.32/2.02  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.32/2.02  tff(c_50, plain, (![A_37, B_38]: (v1_relat_1(k2_zfmisc_1(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.32/2.02  tff(c_80, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.32/2.02  tff(c_240, plain, (![B_102, A_103]: (v1_relat_1(B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(A_103)) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.32/2.02  tff(c_246, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_80, c_240])).
% 5.32/2.02  tff(c_250, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_246])).
% 5.32/2.02  tff(c_52, plain, (![B_40, A_39]: (r1_tarski(k9_relat_1(B_40, A_39), k2_relat_1(B_40)) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.32/2.02  tff(c_60, plain, (![A_45]: (k1_relat_1(A_45)!=k1_xboole_0 | k1_xboole_0=A_45 | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.32/2.02  tff(c_258, plain, (k1_relat_1('#skF_7')!=k1_xboole_0 | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_250, c_60])).
% 5.32/2.02  tff(c_260, plain, (k1_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_258])).
% 5.32/2.02  tff(c_84, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.32/2.02  tff(c_925, plain, (![B_206, A_207]: (k1_tarski(k1_funct_1(B_206, A_207))=k2_relat_1(B_206) | k1_tarski(A_207)!=k1_relat_1(B_206) | ~v1_funct_1(B_206) | ~v1_relat_1(B_206))), inference(cnfTransformation, [status(thm)], [f_131])).
% 5.32/2.02  tff(c_76, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_7', '#skF_6'), k1_tarski(k1_funct_1('#skF_7', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_174])).
% 5.32/2.02  tff(c_936, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_7', '#skF_6'), k2_relat_1('#skF_7')) | k1_tarski('#skF_4')!=k1_relat_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_925, c_76])).
% 5.32/2.02  tff(c_944, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_7', '#skF_6'), k2_relat_1('#skF_7')) | k1_tarski('#skF_4')!=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_250, c_84, c_936])).
% 5.32/2.02  tff(c_1002, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_7')), inference(splitLeft, [status(thm)], [c_944])).
% 5.32/2.02  tff(c_586, plain, (![C_166, A_167, B_168]: (v4_relat_1(C_166, A_167) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.32/2.02  tff(c_595, plain, (v4_relat_1('#skF_7', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_80, c_586])).
% 5.32/2.02  tff(c_349, plain, (![B_119, A_120]: (r1_tarski(k1_relat_1(B_119), A_120) | ~v4_relat_1(B_119, A_120) | ~v1_relat_1(B_119))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.32/2.02  tff(c_22, plain, (![B_21, A_20]: (k1_tarski(B_21)=A_20 | k1_xboole_0=A_20 | ~r1_tarski(A_20, k1_tarski(B_21)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.32/2.02  tff(c_2378, plain, (![B_300, B_301]: (k1_tarski(B_300)=k1_relat_1(B_301) | k1_relat_1(B_301)=k1_xboole_0 | ~v4_relat_1(B_301, k1_tarski(B_300)) | ~v1_relat_1(B_301))), inference(resolution, [status(thm)], [c_349, c_22])).
% 5.32/2.02  tff(c_2416, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_7') | k1_relat_1('#skF_7')=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_595, c_2378])).
% 5.32/2.02  tff(c_2433, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_7') | k1_relat_1('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_250, c_2416])).
% 5.32/2.02  tff(c_2435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_260, c_1002, c_2433])).
% 5.32/2.02  tff(c_2437, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_7')), inference(splitRight, [status(thm)], [c_944])).
% 5.32/2.02  tff(c_2445, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_7'), '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2437, c_80])).
% 5.32/2.02  tff(c_2535, plain, (![A_302, B_303, C_304, D_305]: (k7_relset_1(A_302, B_303, C_304, D_305)=k9_relat_1(C_304, D_305) | ~m1_subset_1(C_304, k1_zfmisc_1(k2_zfmisc_1(A_302, B_303))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.32/2.02  tff(c_2541, plain, (![D_305]: (k7_relset_1(k1_relat_1('#skF_7'), '#skF_5', '#skF_7', D_305)=k9_relat_1('#skF_7', D_305))), inference(resolution, [status(thm)], [c_2445, c_2535])).
% 5.32/2.02  tff(c_2436, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_7', '#skF_6'), k2_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_944])).
% 5.32/2.02  tff(c_2530, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_7'), '#skF_5', '#skF_7', '#skF_6'), k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2437, c_2436])).
% 5.32/2.02  tff(c_2569, plain, (~r1_tarski(k9_relat_1('#skF_7', '#skF_6'), k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2541, c_2530])).
% 5.32/2.02  tff(c_2602, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_52, c_2569])).
% 5.32/2.02  tff(c_2609, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_250, c_2602])).
% 5.32/2.02  tff(c_2610, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_258])).
% 5.32/2.02  tff(c_58, plain, (![A_45]: (k2_relat_1(A_45)!=k1_xboole_0 | k1_xboole_0=A_45 | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_119])).
% 5.32/2.02  tff(c_257, plain, (k2_relat_1('#skF_7')!=k1_xboole_0 | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_250, c_58])).
% 5.32/2.02  tff(c_259, plain, (k2_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_257])).
% 5.32/2.02  tff(c_2612, plain, (k2_relat_1('#skF_7')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2610, c_259])).
% 5.32/2.02  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.32/2.02  tff(c_42, plain, (![A_33]: (v1_xboole_0(k2_relat_1(A_33)) | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.32/2.02  tff(c_114, plain, (![A_89]: (r2_hidden('#skF_3'(A_89), A_89) | k1_xboole_0=A_89)), inference(cnfTransformation, [status(thm)], [f_162])).
% 5.32/2.02  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.32/2.02  tff(c_128, plain, (![A_92]: (~v1_xboole_0(A_92) | k1_xboole_0=A_92)), inference(resolution, [status(thm)], [c_114, c_2])).
% 5.32/2.02  tff(c_138, plain, (![A_93]: (k2_relat_1(A_93)=k1_xboole_0 | ~v1_xboole_0(A_93))), inference(resolution, [status(thm)], [c_42, c_128])).
% 5.32/2.02  tff(c_146, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_138])).
% 5.32/2.02  tff(c_2616, plain, (k2_relat_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2610, c_2610, c_146])).
% 5.32/2.02  tff(c_2653, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2612, c_2616])).
% 5.32/2.02  tff(c_2654, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_257])).
% 5.32/2.02  tff(c_2665, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2654, c_12])).
% 5.32/2.02  tff(c_2655, plain, (k2_relat_1('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_257])).
% 5.32/2.02  tff(c_2677, plain, (k2_relat_1('#skF_7')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_2654, c_2655])).
% 5.32/2.02  tff(c_2760, plain, (![B_319, A_320]: (r1_tarski(k9_relat_1(B_319, A_320), k2_relat_1(B_319)) | ~v1_relat_1(B_319))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.32/2.02  tff(c_2766, plain, (![A_320]: (r1_tarski(k9_relat_1('#skF_7', A_320), '#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2677, c_2760])).
% 5.32/2.02  tff(c_2768, plain, (![A_320]: (r1_tarski(k9_relat_1('#skF_7', A_320), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_250, c_2766])).
% 5.32/2.02  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.32/2.02  tff(c_30, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.32/2.02  tff(c_2937, plain, (![C_347, B_348, A_349]: (~v1_xboole_0(C_347) | ~m1_subset_1(B_348, k1_zfmisc_1(C_347)) | ~r2_hidden(A_349, B_348))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.32/2.02  tff(c_2960, plain, (![B_353, A_354, A_355]: (~v1_xboole_0(B_353) | ~r2_hidden(A_354, A_355) | ~r1_tarski(A_355, B_353))), inference(resolution, [status(thm)], [c_30, c_2937])).
% 5.32/2.02  tff(c_2970, plain, (![B_356, A_357]: (~v1_xboole_0(B_356) | ~r1_tarski(A_357, B_356) | v1_xboole_0(A_357))), inference(resolution, [status(thm)], [c_4, c_2960])).
% 5.32/2.02  tff(c_2979, plain, (![A_320]: (~v1_xboole_0('#skF_7') | v1_xboole_0(k9_relat_1('#skF_7', A_320)))), inference(resolution, [status(thm)], [c_2768, c_2970])).
% 5.32/2.02  tff(c_3004, plain, (![A_358]: (v1_xboole_0(k9_relat_1('#skF_7', A_358)))), inference(demodulation, [status(thm), theory('equality')], [c_2665, c_2979])).
% 5.32/2.02  tff(c_118, plain, (![A_89]: (~v1_xboole_0(A_89) | k1_xboole_0=A_89)), inference(resolution, [status(thm)], [c_114, c_2])).
% 5.32/2.02  tff(c_2661, plain, (![A_89]: (~v1_xboole_0(A_89) | A_89='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2654, c_118])).
% 5.32/2.02  tff(c_3015, plain, (![A_358]: (k9_relat_1('#skF_7', A_358)='#skF_7')), inference(resolution, [status(thm)], [c_3004, c_2661])).
% 5.32/2.02  tff(c_3661, plain, (![A_448, B_449, C_450, D_451]: (k7_relset_1(A_448, B_449, C_450, D_451)=k9_relat_1(C_450, D_451) | ~m1_subset_1(C_450, k1_zfmisc_1(k2_zfmisc_1(A_448, B_449))))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.32/2.02  tff(c_3666, plain, (![D_451]: (k7_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_7', D_451)=k9_relat_1('#skF_7', D_451))), inference(resolution, [status(thm)], [c_80, c_3661])).
% 5.32/2.02  tff(c_3669, plain, (![D_451]: (k7_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_7', D_451)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3015, c_3666])).
% 5.32/2.02  tff(c_2692, plain, (![A_310, B_311]: (r2_hidden('#skF_2'(A_310, B_311), A_310) | r1_tarski(A_310, B_311))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.32/2.02  tff(c_2710, plain, (![A_314, B_315]: (~v1_xboole_0(A_314) | r1_tarski(A_314, B_315))), inference(resolution, [status(thm)], [c_2692, c_2])).
% 5.32/2.02  tff(c_2714, plain, (~v1_xboole_0(k7_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_2710, c_76])).
% 5.32/2.02  tff(c_3670, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3669, c_2714])).
% 5.32/2.02  tff(c_3674, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2665, c_3670])).
% 5.32/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.32/2.02  
% 5.32/2.02  Inference rules
% 5.32/2.02  ----------------------
% 5.32/2.02  #Ref     : 0
% 5.32/2.02  #Sup     : 759
% 5.32/2.02  #Fact    : 0
% 5.32/2.02  #Define  : 0
% 5.32/2.02  #Split   : 18
% 5.32/2.02  #Chain   : 0
% 5.32/2.02  #Close   : 0
% 5.32/2.02  
% 5.32/2.02  Ordering : KBO
% 5.32/2.02  
% 5.32/2.02  Simplification rules
% 5.32/2.02  ----------------------
% 5.32/2.02  #Subsume      : 280
% 5.32/2.02  #Demod        : 605
% 5.32/2.02  #Tautology    : 353
% 5.32/2.02  #SimpNegUnit  : 76
% 5.32/2.02  #BackRed      : 71
% 5.32/2.02  
% 5.32/2.02  #Partial instantiations: 0
% 5.32/2.02  #Strategies tried      : 1
% 5.32/2.02  
% 5.32/2.02  Timing (in seconds)
% 5.32/2.02  ----------------------
% 5.32/2.02  Preprocessing        : 0.38
% 5.32/2.02  Parsing              : 0.20
% 5.32/2.02  CNF conversion       : 0.03
% 5.32/2.02  Main loop            : 0.82
% 5.32/2.02  Inferencing          : 0.29
% 5.32/2.02  Reduction            : 0.27
% 5.32/2.02  Demodulation         : 0.19
% 5.32/2.02  BG Simplification    : 0.03
% 5.32/2.02  Subsumption          : 0.15
% 5.32/2.02  Abstraction          : 0.03
% 5.32/2.02  MUC search           : 0.00
% 5.32/2.02  Cooper               : 0.00
% 5.32/2.02  Total                : 1.24
% 5.32/2.02  Index Insertion      : 0.00
% 5.32/2.02  Index Deletion       : 0.00
% 5.32/2.02  Index Matching       : 0.00
% 5.32/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
