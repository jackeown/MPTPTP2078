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
% DateTime   : Thu Dec  3 10:14:48 EST 2020

% Result     : Theorem 4.79s
% Output     : CNFRefutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 192 expanded)
%              Number of leaves         :   41 (  83 expanded)
%              Depth                    :   10
%              Number of atoms          :  161 ( 403 expanded)
%              Number of equality atoms :   84 ( 139 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_66,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_32,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_98,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_106,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(resolution,[status(thm)],[c_32,c_98])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_223,plain,(
    ! [C_81,A_82,B_83] :
      ( v1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_236,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_223])).

tff(c_44,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k9_relat_1(B_22,A_21),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_46,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) = k1_xboole_0
      | k2_relat_1(A_23) != k1_xboole_0
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_244,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_236,c_46])).

tff(c_254,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_48,plain,(
    ! [A_23] :
      ( k2_relat_1(A_23) = k1_xboole_0
      | k1_relat_1(A_23) != k1_xboole_0
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_245,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_236,c_48])).

tff(c_342,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_245])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_582,plain,(
    ! [B_138,A_139] :
      ( k1_tarski(k1_funct_1(B_138,A_139)) = k2_relat_1(B_138)
      | k1_tarski(A_139) != k1_relat_1(B_138)
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_60,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_591,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_582,c_60])).

tff(c_609,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_68,c_591])).

tff(c_614,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_609])).

tff(c_386,plain,(
    ! [C_102,A_103,B_104] :
      ( v4_relat_1(C_102,A_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_399,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_386])).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_42,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(B_20),A_19)
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10,plain,(
    ! [A_4,B_5] : k1_enumset1(A_4,A_4,B_5) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_700,plain,(
    ! [A_164,B_165,C_166,D_167] :
      ( k1_enumset1(A_164,B_165,C_166) = D_167
      | k2_tarski(A_164,C_166) = D_167
      | k2_tarski(B_165,C_166) = D_167
      | k2_tarski(A_164,B_165) = D_167
      | k1_tarski(C_166) = D_167
      | k1_tarski(B_165) = D_167
      | k1_tarski(A_164) = D_167
      | k1_xboole_0 = D_167
      | ~ r1_tarski(D_167,k1_enumset1(A_164,B_165,C_166)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_729,plain,(
    ! [A_4,B_5,D_167] :
      ( k1_enumset1(A_4,A_4,B_5) = D_167
      | k2_tarski(A_4,B_5) = D_167
      | k2_tarski(A_4,B_5) = D_167
      | k2_tarski(A_4,A_4) = D_167
      | k1_tarski(B_5) = D_167
      | k1_tarski(A_4) = D_167
      | k1_tarski(A_4) = D_167
      | k1_xboole_0 = D_167
      | ~ r1_tarski(D_167,k2_tarski(A_4,B_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_700])).

tff(c_1593,plain,(
    ! [A_308,B_309,D_310] :
      ( k2_tarski(A_308,B_309) = D_310
      | k2_tarski(A_308,B_309) = D_310
      | k2_tarski(A_308,B_309) = D_310
      | k1_tarski(A_308) = D_310
      | k1_tarski(B_309) = D_310
      | k1_tarski(A_308) = D_310
      | k1_tarski(A_308) = D_310
      | k1_xboole_0 = D_310
      | ~ r1_tarski(D_310,k2_tarski(A_308,B_309)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10,c_729])).

tff(c_2218,plain,(
    ! [A_399,B_400,B_401] :
      ( k2_tarski(A_399,B_400) = k1_relat_1(B_401)
      | k1_tarski(B_400) = k1_relat_1(B_401)
      | k1_tarski(A_399) = k1_relat_1(B_401)
      | k1_relat_1(B_401) = k1_xboole_0
      | ~ v4_relat_1(B_401,k2_tarski(A_399,B_400))
      | ~ v1_relat_1(B_401) ) ),
    inference(resolution,[status(thm)],[c_42,c_1593])).

tff(c_2273,plain,(
    ! [A_3,B_401] :
      ( k2_tarski(A_3,A_3) = k1_relat_1(B_401)
      | k1_tarski(A_3) = k1_relat_1(B_401)
      | k1_tarski(A_3) = k1_relat_1(B_401)
      | k1_relat_1(B_401) = k1_xboole_0
      | ~ v4_relat_1(B_401,k1_tarski(A_3))
      | ~ v1_relat_1(B_401) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_2218])).

tff(c_2314,plain,(
    ! [A_402,B_403] :
      ( k1_tarski(A_402) = k1_relat_1(B_403)
      | k1_tarski(A_402) = k1_relat_1(B_403)
      | k1_tarski(A_402) = k1_relat_1(B_403)
      | k1_relat_1(B_403) = k1_xboole_0
      | ~ v4_relat_1(B_403,k1_tarski(A_402))
      | ~ v1_relat_1(B_403) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2273])).

tff(c_2368,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_399,c_2314])).

tff(c_2411,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_2368])).

tff(c_2413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_614,c_2411])).

tff(c_2415,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_609])).

tff(c_2421,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2415,c_64])).

tff(c_58,plain,(
    ! [A_32,B_33,C_34,D_35] :
      ( k7_relset_1(A_32,B_33,C_34,D_35) = k9_relat_1(C_34,D_35)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2535,plain,(
    ! [D_35] : k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4',D_35) = k9_relat_1('#skF_4',D_35) ),
    inference(resolution,[status(thm)],[c_2421,c_58])).

tff(c_2414,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_609])).

tff(c_2684,plain,(
    ~ r1_tarski(k7_relset_1(k1_relat_1('#skF_4'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2415,c_2414])).

tff(c_2685,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2535,c_2684])).

tff(c_2698,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_2685])).

tff(c_2702,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_2698])).

tff(c_2704,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_2712,plain,(
    ! [A_21] :
      ( r1_tarski(k9_relat_1('#skF_4',A_21),k1_xboole_0)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2704,c_44])).

tff(c_2732,plain,(
    ! [A_435] : r1_tarski(k9_relat_1('#skF_4',A_435),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_2712])).

tff(c_157,plain,(
    ! [B_71,A_72] :
      ( B_71 = A_72
      | ~ r1_tarski(B_71,A_72)
      | ~ r1_tarski(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_186,plain,(
    ! [A_13] :
      ( k1_xboole_0 = A_13
      | ~ r1_tarski(A_13,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_106,c_157])).

tff(c_2738,plain,(
    ! [A_435] : k9_relat_1('#skF_4',A_435) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2732,c_186])).

tff(c_3280,plain,(
    ! [A_525,B_526,C_527,D_528] :
      ( k7_relset_1(A_525,B_526,C_527,D_528) = k9_relat_1(C_527,D_528)
      | ~ m1_subset_1(C_527,k1_zfmisc_1(k2_zfmisc_1(A_525,B_526))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_3285,plain,(
    ! [D_528] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_528) = k9_relat_1('#skF_4',D_528) ),
    inference(resolution,[status(thm)],[c_64,c_3280])).

tff(c_3291,plain,(
    ! [D_528] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_528) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2738,c_3285])).

tff(c_3301,plain,(
    ~ r1_tarski(k1_xboole_0,k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3291,c_60])).

tff(c_3304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_3301])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:27:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.79/1.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.92  
% 4.79/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.79/1.92  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.79/1.92  
% 4.79/1.92  %Foreground sorts:
% 4.79/1.92  
% 4.79/1.92  
% 4.79/1.92  %Background operators:
% 4.79/1.92  
% 4.79/1.92  
% 4.79/1.92  %Foreground operators:
% 4.79/1.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.79/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.79/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.79/1.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.79/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.79/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.79/1.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.79/1.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.79/1.92  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.79/1.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.79/1.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.79/1.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.79/1.92  tff('#skF_2', type, '#skF_2': $i).
% 4.79/1.92  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.79/1.92  tff('#skF_3', type, '#skF_3': $i).
% 4.79/1.92  tff('#skF_1', type, '#skF_1': $i).
% 4.79/1.92  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.79/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.79/1.92  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.79/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.79/1.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.79/1.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.79/1.92  tff('#skF_4', type, '#skF_4': $i).
% 4.79/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.79/1.92  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.79/1.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.79/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.79/1.92  
% 5.14/1.94  tff(f_66, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.14/1.94  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.14/1.94  tff(f_126, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 5.14/1.94  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.14/1.94  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 5.14/1.94  tff(f_92, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 5.14/1.94  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 5.14/1.94  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.14/1.94  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.14/1.94  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 5.14/1.94  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 5.14/1.94  tff(f_64, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 5.14/1.94  tff(f_114, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.14/1.94  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.14/1.94  tff(c_32, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.14/1.94  tff(c_98, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.14/1.94  tff(c_106, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(resolution, [status(thm)], [c_32, c_98])).
% 5.14/1.94  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.14/1.94  tff(c_223, plain, (![C_81, A_82, B_83]: (v1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.14/1.94  tff(c_236, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_223])).
% 5.14/1.94  tff(c_44, plain, (![B_22, A_21]: (r1_tarski(k9_relat_1(B_22, A_21), k2_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.14/1.94  tff(c_46, plain, (![A_23]: (k1_relat_1(A_23)=k1_xboole_0 | k2_relat_1(A_23)!=k1_xboole_0 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.14/1.94  tff(c_244, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_236, c_46])).
% 5.14/1.94  tff(c_254, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_244])).
% 5.14/1.94  tff(c_48, plain, (![A_23]: (k2_relat_1(A_23)=k1_xboole_0 | k1_relat_1(A_23)!=k1_xboole_0 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.14/1.94  tff(c_245, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_236, c_48])).
% 5.14/1.94  tff(c_342, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_254, c_245])).
% 5.14/1.94  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.14/1.94  tff(c_582, plain, (![B_138, A_139]: (k1_tarski(k1_funct_1(B_138, A_139))=k2_relat_1(B_138) | k1_tarski(A_139)!=k1_relat_1(B_138) | ~v1_funct_1(B_138) | ~v1_relat_1(B_138))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.14/1.94  tff(c_60, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.14/1.94  tff(c_591, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_582, c_60])).
% 5.14/1.94  tff(c_609, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_236, c_68, c_591])).
% 5.14/1.94  tff(c_614, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_609])).
% 5.14/1.94  tff(c_386, plain, (![C_102, A_103, B_104]: (v4_relat_1(C_102, A_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.14/1.94  tff(c_399, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_386])).
% 5.14/1.94  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.14/1.94  tff(c_42, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(B_20), A_19) | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.14/1.94  tff(c_10, plain, (![A_4, B_5]: (k1_enumset1(A_4, A_4, B_5)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.14/1.94  tff(c_700, plain, (![A_164, B_165, C_166, D_167]: (k1_enumset1(A_164, B_165, C_166)=D_167 | k2_tarski(A_164, C_166)=D_167 | k2_tarski(B_165, C_166)=D_167 | k2_tarski(A_164, B_165)=D_167 | k1_tarski(C_166)=D_167 | k1_tarski(B_165)=D_167 | k1_tarski(A_164)=D_167 | k1_xboole_0=D_167 | ~r1_tarski(D_167, k1_enumset1(A_164, B_165, C_166)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.14/1.94  tff(c_729, plain, (![A_4, B_5, D_167]: (k1_enumset1(A_4, A_4, B_5)=D_167 | k2_tarski(A_4, B_5)=D_167 | k2_tarski(A_4, B_5)=D_167 | k2_tarski(A_4, A_4)=D_167 | k1_tarski(B_5)=D_167 | k1_tarski(A_4)=D_167 | k1_tarski(A_4)=D_167 | k1_xboole_0=D_167 | ~r1_tarski(D_167, k2_tarski(A_4, B_5)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_700])).
% 5.14/1.94  tff(c_1593, plain, (![A_308, B_309, D_310]: (k2_tarski(A_308, B_309)=D_310 | k2_tarski(A_308, B_309)=D_310 | k2_tarski(A_308, B_309)=D_310 | k1_tarski(A_308)=D_310 | k1_tarski(B_309)=D_310 | k1_tarski(A_308)=D_310 | k1_tarski(A_308)=D_310 | k1_xboole_0=D_310 | ~r1_tarski(D_310, k2_tarski(A_308, B_309)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10, c_729])).
% 5.14/1.94  tff(c_2218, plain, (![A_399, B_400, B_401]: (k2_tarski(A_399, B_400)=k1_relat_1(B_401) | k1_tarski(B_400)=k1_relat_1(B_401) | k1_tarski(A_399)=k1_relat_1(B_401) | k1_relat_1(B_401)=k1_xboole_0 | ~v4_relat_1(B_401, k2_tarski(A_399, B_400)) | ~v1_relat_1(B_401))), inference(resolution, [status(thm)], [c_42, c_1593])).
% 5.14/1.94  tff(c_2273, plain, (![A_3, B_401]: (k2_tarski(A_3, A_3)=k1_relat_1(B_401) | k1_tarski(A_3)=k1_relat_1(B_401) | k1_tarski(A_3)=k1_relat_1(B_401) | k1_relat_1(B_401)=k1_xboole_0 | ~v4_relat_1(B_401, k1_tarski(A_3)) | ~v1_relat_1(B_401))), inference(superposition, [status(thm), theory('equality')], [c_8, c_2218])).
% 5.14/1.94  tff(c_2314, plain, (![A_402, B_403]: (k1_tarski(A_402)=k1_relat_1(B_403) | k1_tarski(A_402)=k1_relat_1(B_403) | k1_tarski(A_402)=k1_relat_1(B_403) | k1_relat_1(B_403)=k1_xboole_0 | ~v4_relat_1(B_403, k1_tarski(A_402)) | ~v1_relat_1(B_403))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2273])).
% 5.14/1.94  tff(c_2368, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_399, c_2314])).
% 5.14/1.94  tff(c_2411, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_236, c_2368])).
% 5.14/1.94  tff(c_2413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_342, c_614, c_2411])).
% 5.14/1.94  tff(c_2415, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_609])).
% 5.14/1.94  tff(c_2421, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2415, c_64])).
% 5.14/1.94  tff(c_58, plain, (![A_32, B_33, C_34, D_35]: (k7_relset_1(A_32, B_33, C_34, D_35)=k9_relat_1(C_34, D_35) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.14/1.94  tff(c_2535, plain, (![D_35]: (k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', D_35)=k9_relat_1('#skF_4', D_35))), inference(resolution, [status(thm)], [c_2421, c_58])).
% 5.14/1.94  tff(c_2414, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_609])).
% 5.14/1.94  tff(c_2684, plain, (~r1_tarski(k7_relset_1(k1_relat_1('#skF_4'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2415, c_2414])).
% 5.14/1.94  tff(c_2685, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2535, c_2684])).
% 5.14/1.94  tff(c_2698, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_2685])).
% 5.14/1.94  tff(c_2702, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_236, c_2698])).
% 5.14/1.94  tff(c_2704, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_244])).
% 5.14/1.94  tff(c_2712, plain, (![A_21]: (r1_tarski(k9_relat_1('#skF_4', A_21), k1_xboole_0) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2704, c_44])).
% 5.14/1.94  tff(c_2732, plain, (![A_435]: (r1_tarski(k9_relat_1('#skF_4', A_435), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_2712])).
% 5.14/1.94  tff(c_157, plain, (![B_71, A_72]: (B_71=A_72 | ~r1_tarski(B_71, A_72) | ~r1_tarski(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.14/1.94  tff(c_186, plain, (![A_13]: (k1_xboole_0=A_13 | ~r1_tarski(A_13, k1_xboole_0))), inference(resolution, [status(thm)], [c_106, c_157])).
% 5.14/1.94  tff(c_2738, plain, (![A_435]: (k9_relat_1('#skF_4', A_435)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2732, c_186])).
% 5.14/1.94  tff(c_3280, plain, (![A_525, B_526, C_527, D_528]: (k7_relset_1(A_525, B_526, C_527, D_528)=k9_relat_1(C_527, D_528) | ~m1_subset_1(C_527, k1_zfmisc_1(k2_zfmisc_1(A_525, B_526))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.14/1.94  tff(c_3285, plain, (![D_528]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_528)=k9_relat_1('#skF_4', D_528))), inference(resolution, [status(thm)], [c_64, c_3280])).
% 5.14/1.94  tff(c_3291, plain, (![D_528]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_528)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2738, c_3285])).
% 5.14/1.94  tff(c_3301, plain, (~r1_tarski(k1_xboole_0, k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3291, c_60])).
% 5.14/1.94  tff(c_3304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_3301])).
% 5.14/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.14/1.94  
% 5.14/1.94  Inference rules
% 5.14/1.94  ----------------------
% 5.14/1.94  #Ref     : 0
% 5.14/1.94  #Sup     : 616
% 5.14/1.94  #Fact    : 0
% 5.14/1.94  #Define  : 0
% 5.14/1.94  #Split   : 6
% 5.14/1.94  #Chain   : 0
% 5.14/1.94  #Close   : 0
% 5.14/1.94  
% 5.14/1.94  Ordering : KBO
% 5.14/1.94  
% 5.14/1.94  Simplification rules
% 5.14/1.94  ----------------------
% 5.14/1.94  #Subsume      : 50
% 5.14/1.94  #Demod        : 819
% 5.14/1.94  #Tautology    : 331
% 5.14/1.94  #SimpNegUnit  : 10
% 5.14/1.94  #BackRed      : 14
% 5.14/1.94  
% 5.14/1.94  #Partial instantiations: 0
% 5.14/1.94  #Strategies tried      : 1
% 5.14/1.94  
% 5.14/1.94  Timing (in seconds)
% 5.14/1.94  ----------------------
% 5.14/1.94  Preprocessing        : 0.34
% 5.14/1.94  Parsing              : 0.18
% 5.14/1.94  CNF conversion       : 0.02
% 5.14/1.95  Main loop            : 0.84
% 5.14/1.95  Inferencing          : 0.31
% 5.14/1.95  Reduction            : 0.31
% 5.14/1.95  Demodulation         : 0.24
% 5.14/1.95  BG Simplification    : 0.03
% 5.14/1.95  Subsumption          : 0.13
% 5.14/1.95  Abstraction          : 0.06
% 5.14/1.95  MUC search           : 0.00
% 5.14/1.95  Cooper               : 0.00
% 5.14/1.95  Total                : 1.21
% 5.14/1.95  Index Insertion      : 0.00
% 5.14/1.95  Index Deletion       : 0.00
% 5.14/1.95  Index Matching       : 0.00
% 5.14/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
