%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:02 EST 2020

% Result     : Theorem 4.54s
% Output     : CNFRefutation 4.74s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 178 expanded)
%              Number of leaves         :   54 (  85 expanded)
%              Depth                    :   10
%              Number of atoms          :  142 ( 340 expanded)
%              Number of equality atoms :   56 ( 116 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_150,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_138,axiom,(
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

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_84,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_102,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_100,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_264,plain,(
    ! [A_155,B_156,C_157] :
      ( k1_relset_1(A_155,B_156,C_157) = k1_relat_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_273,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_264])).

tff(c_1199,plain,(
    ! [B_304,A_305,C_306] :
      ( k1_xboole_0 = B_304
      | k1_relset_1(A_305,B_304,C_306) = A_305
      | ~ v1_funct_2(C_306,A_305,B_304)
      | ~ m1_subset_1(C_306,k1_zfmisc_1(k2_zfmisc_1(A_305,B_304))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1213,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_1199])).

tff(c_1219,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_273,c_1213])).

tff(c_1220,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_1219])).

tff(c_889,plain,(
    ! [D_279,C_280,B_281,A_282] :
      ( m1_subset_1(D_279,k1_zfmisc_1(k2_zfmisc_1(C_280,B_281)))
      | ~ r1_tarski(k2_relat_1(D_279),B_281)
      | ~ m1_subset_1(D_279,k1_zfmisc_1(k2_zfmisc_1(C_280,A_282))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_986,plain,(
    ! [B_289] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),B_289)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_289) ) ),
    inference(resolution,[status(thm)],[c_100,c_889])).

tff(c_76,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( k7_relset_1(A_62,B_63,C_64,D_65) = k9_relat_1(C_64,D_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1190,plain,(
    ! [B_302,D_303] :
      ( k7_relset_1(k1_tarski('#skF_3'),B_302,'#skF_6',D_303) = k9_relat_1('#skF_6',D_303)
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_302) ) ),
    inference(resolution,[status(thm)],[c_986,c_76])).

tff(c_1198,plain,(
    ! [D_303] : k7_relset_1(k1_tarski('#skF_3'),k2_relat_1('#skF_6'),'#skF_6',D_303) = k9_relat_1('#skF_6',D_303) ),
    inference(resolution,[status(thm)],[c_6,c_1190])).

tff(c_1569,plain,(
    ! [D_303] : k7_relset_1(k1_relat_1('#skF_6'),k2_relat_1('#skF_6'),'#skF_6',D_303) = k9_relat_1('#skF_6',D_303) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1220,c_1198])).

tff(c_900,plain,(
    ! [B_281] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),B_281)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_281) ) ),
    inference(resolution,[status(thm)],[c_100,c_889])).

tff(c_1585,plain,(
    ! [B_331] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),B_331)))
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_331) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1220,c_900])).

tff(c_346,plain,(
    ! [A_181,B_182,C_183,D_184] :
      ( m1_subset_1(k7_relset_1(A_181,B_182,C_183,D_184),k1_zfmisc_1(B_182))
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_58,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_369,plain,(
    ! [A_181,B_182,C_183,D_184] :
      ( r1_tarski(k7_relset_1(A_181,B_182,C_183,D_184),B_182)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(resolution,[status(thm)],[c_346,c_58])).

tff(c_1750,plain,(
    ! [B_348,D_349] :
      ( r1_tarski(k7_relset_1(k1_relat_1('#skF_6'),B_348,'#skF_6',D_349),B_348)
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_348) ) ),
    inference(resolution,[status(thm)],[c_1585,c_369])).

tff(c_1790,plain,(
    ! [D_303] :
      ( r1_tarski(k9_relat_1('#skF_6',D_303),k2_relat_1('#skF_6'))
      | ~ r1_tarski(k2_relat_1('#skF_6'),k2_relat_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1569,c_1750])).

tff(c_1806,plain,(
    ! [D_303] : r1_tarski(k9_relat_1('#skF_6',D_303),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1790])).

tff(c_66,plain,(
    ! [A_48,B_49] : v1_relat_1(k2_zfmisc_1(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_151,plain,(
    ! [B_113,A_114] :
      ( v1_relat_1(B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_114))
      | ~ v1_relat_1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_157,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_100,c_151])).

tff(c_161,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_157])).

tff(c_104,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_398,plain,(
    ! [A_193,B_194,C_195,D_196] :
      ( k7_relset_1(A_193,B_194,C_195,D_196) = k9_relat_1(C_195,D_196)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_409,plain,(
    ! [D_196] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_196) = k9_relat_1('#skF_6',D_196) ),
    inference(resolution,[status(thm)],[c_100,c_398])).

tff(c_219,plain,(
    ! [A_130,B_131,C_132] :
      ( k2_relset_1(A_130,B_131,C_132) = k2_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_228,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_219])).

tff(c_752,plain,(
    ! [A_268,B_269,C_270] :
      ( k7_relset_1(A_268,B_269,C_270,A_268) = k2_relset_1(A_268,B_269,C_270)
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_zfmisc_1(A_268,B_269))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_760,plain,(
    k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',k1_tarski('#skF_3')) = k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_100,c_752])).

tff(c_764,plain,(
    k9_relat_1('#skF_6',k1_tarski('#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_228,c_760])).

tff(c_64,plain,(
    ! [A_45,B_47] :
      ( k9_relat_1(A_45,k1_tarski(B_47)) = k11_relat_1(A_45,B_47)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_775,plain,
    ( k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_764,c_64])).

tff(c_783,plain,(
    k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_775])).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4,B_5] : k1_enumset1(A_4,A_4,B_5) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_6,B_7,C_8] : k2_enumset1(A_6,A_6,B_7,C_8) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_191,plain,(
    ! [A_122,B_123,C_124,D_125] : k3_enumset1(A_122,A_122,B_123,C_124,D_125) = k2_enumset1(A_122,B_123,C_124,D_125) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [A_31,G_39,C_33,B_32,E_35] : r2_hidden(G_39,k3_enumset1(A_31,B_32,C_33,G_39,E_35)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_215,plain,(
    ! [C_126,A_127,B_128,D_129] : r2_hidden(C_126,k2_enumset1(A_127,B_128,C_126,D_129)) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_26])).

tff(c_229,plain,(
    ! [B_133,A_134,C_135] : r2_hidden(B_133,k1_enumset1(A_134,B_133,C_135)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_215])).

tff(c_233,plain,(
    ! [A_136,B_137] : r2_hidden(A_136,k2_tarski(A_136,B_137)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_229])).

tff(c_236,plain,(
    ! [A_3] : r2_hidden(A_3,k1_tarski(A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_233])).

tff(c_1244,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1220,c_236])).

tff(c_68,plain,(
    ! [B_51,A_50] :
      ( k1_tarski(k1_funct_1(B_51,A_50)) = k11_relat_1(B_51,A_50)
      | ~ r2_hidden(A_50,k1_relat_1(B_51))
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1254,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1244,c_68])).

tff(c_1257,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_104,c_783,c_1254])).

tff(c_96,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_411,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_96])).

tff(c_1351,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1257,c_411])).

tff(c_1811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1806,c_1351])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.54/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.84  
% 4.54/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.85  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 4.54/1.85  
% 4.54/1.85  %Foreground sorts:
% 4.54/1.85  
% 4.54/1.85  
% 4.54/1.85  %Background operators:
% 4.54/1.85  
% 4.54/1.85  
% 4.54/1.85  %Foreground operators:
% 4.54/1.85  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.54/1.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.54/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.54/1.85  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 4.54/1.85  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 4.54/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.54/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.54/1.85  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.54/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.54/1.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.54/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.54/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.54/1.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.54/1.85  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.54/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.54/1.85  tff('#skF_5', type, '#skF_5': $i).
% 4.54/1.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.54/1.85  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 4.54/1.85  tff('#skF_6', type, '#skF_6': $i).
% 4.54/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.54/1.85  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.54/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.54/1.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.54/1.85  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.54/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.54/1.85  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.54/1.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.54/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.54/1.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.54/1.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.54/1.85  tff('#skF_4', type, '#skF_4': $i).
% 4.54/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.54/1.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.54/1.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.54/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.54/1.85  
% 4.74/1.88  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.74/1.88  tff(f_150, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 4.74/1.88  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.74/1.88  tff(f_138, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.74/1.88  tff(f_114, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 4.74/1.88  tff(f_108, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.74/1.88  tff(f_96, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 4.74/1.88  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.74/1.88  tff(f_84, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.74/1.88  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.74/1.88  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.74/1.88  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 4.74/1.88  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 4.74/1.88  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.74/1.88  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.74/1.88  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.74/1.88  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 4.74/1.88  tff(f_66, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_enumset1)).
% 4.74/1.88  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 4.74/1.88  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.74/1.88  tff(c_98, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.74/1.88  tff(c_102, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.74/1.88  tff(c_100, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.74/1.88  tff(c_264, plain, (![A_155, B_156, C_157]: (k1_relset_1(A_155, B_156, C_157)=k1_relat_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.74/1.88  tff(c_273, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_100, c_264])).
% 4.74/1.88  tff(c_1199, plain, (![B_304, A_305, C_306]: (k1_xboole_0=B_304 | k1_relset_1(A_305, B_304, C_306)=A_305 | ~v1_funct_2(C_306, A_305, B_304) | ~m1_subset_1(C_306, k1_zfmisc_1(k2_zfmisc_1(A_305, B_304))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.74/1.88  tff(c_1213, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_100, c_1199])).
% 4.74/1.88  tff(c_1219, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_273, c_1213])).
% 4.74/1.88  tff(c_1220, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_98, c_1219])).
% 4.74/1.88  tff(c_889, plain, (![D_279, C_280, B_281, A_282]: (m1_subset_1(D_279, k1_zfmisc_1(k2_zfmisc_1(C_280, B_281))) | ~r1_tarski(k2_relat_1(D_279), B_281) | ~m1_subset_1(D_279, k1_zfmisc_1(k2_zfmisc_1(C_280, A_282))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.74/1.88  tff(c_986, plain, (![B_289]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), B_289))) | ~r1_tarski(k2_relat_1('#skF_6'), B_289))), inference(resolution, [status(thm)], [c_100, c_889])).
% 4.74/1.88  tff(c_76, plain, (![A_62, B_63, C_64, D_65]: (k7_relset_1(A_62, B_63, C_64, D_65)=k9_relat_1(C_64, D_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.74/1.88  tff(c_1190, plain, (![B_302, D_303]: (k7_relset_1(k1_tarski('#skF_3'), B_302, '#skF_6', D_303)=k9_relat_1('#skF_6', D_303) | ~r1_tarski(k2_relat_1('#skF_6'), B_302))), inference(resolution, [status(thm)], [c_986, c_76])).
% 4.74/1.88  tff(c_1198, plain, (![D_303]: (k7_relset_1(k1_tarski('#skF_3'), k2_relat_1('#skF_6'), '#skF_6', D_303)=k9_relat_1('#skF_6', D_303))), inference(resolution, [status(thm)], [c_6, c_1190])).
% 4.74/1.88  tff(c_1569, plain, (![D_303]: (k7_relset_1(k1_relat_1('#skF_6'), k2_relat_1('#skF_6'), '#skF_6', D_303)=k9_relat_1('#skF_6', D_303))), inference(demodulation, [status(thm), theory('equality')], [c_1220, c_1198])).
% 4.74/1.88  tff(c_900, plain, (![B_281]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), B_281))) | ~r1_tarski(k2_relat_1('#skF_6'), B_281))), inference(resolution, [status(thm)], [c_100, c_889])).
% 4.74/1.88  tff(c_1585, plain, (![B_331]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), B_331))) | ~r1_tarski(k2_relat_1('#skF_6'), B_331))), inference(demodulation, [status(thm), theory('equality')], [c_1220, c_900])).
% 4.74/1.88  tff(c_346, plain, (![A_181, B_182, C_183, D_184]: (m1_subset_1(k7_relset_1(A_181, B_182, C_183, D_184), k1_zfmisc_1(B_182)) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.74/1.88  tff(c_58, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.74/1.88  tff(c_369, plain, (![A_181, B_182, C_183, D_184]: (r1_tarski(k7_relset_1(A_181, B_182, C_183, D_184), B_182) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(resolution, [status(thm)], [c_346, c_58])).
% 4.74/1.88  tff(c_1750, plain, (![B_348, D_349]: (r1_tarski(k7_relset_1(k1_relat_1('#skF_6'), B_348, '#skF_6', D_349), B_348) | ~r1_tarski(k2_relat_1('#skF_6'), B_348))), inference(resolution, [status(thm)], [c_1585, c_369])).
% 4.74/1.88  tff(c_1790, plain, (![D_303]: (r1_tarski(k9_relat_1('#skF_6', D_303), k2_relat_1('#skF_6')) | ~r1_tarski(k2_relat_1('#skF_6'), k2_relat_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1569, c_1750])).
% 4.74/1.88  tff(c_1806, plain, (![D_303]: (r1_tarski(k9_relat_1('#skF_6', D_303), k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1790])).
% 4.74/1.88  tff(c_66, plain, (![A_48, B_49]: (v1_relat_1(k2_zfmisc_1(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.74/1.88  tff(c_151, plain, (![B_113, A_114]: (v1_relat_1(B_113) | ~m1_subset_1(B_113, k1_zfmisc_1(A_114)) | ~v1_relat_1(A_114))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.74/1.88  tff(c_157, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_100, c_151])).
% 4.74/1.88  tff(c_161, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_157])).
% 4.74/1.88  tff(c_104, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.74/1.88  tff(c_398, plain, (![A_193, B_194, C_195, D_196]: (k7_relset_1(A_193, B_194, C_195, D_196)=k9_relat_1(C_195, D_196) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.74/1.88  tff(c_409, plain, (![D_196]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_196)=k9_relat_1('#skF_6', D_196))), inference(resolution, [status(thm)], [c_100, c_398])).
% 4.74/1.88  tff(c_219, plain, (![A_130, B_131, C_132]: (k2_relset_1(A_130, B_131, C_132)=k2_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.74/1.88  tff(c_228, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_100, c_219])).
% 4.74/1.88  tff(c_752, plain, (![A_268, B_269, C_270]: (k7_relset_1(A_268, B_269, C_270, A_268)=k2_relset_1(A_268, B_269, C_270) | ~m1_subset_1(C_270, k1_zfmisc_1(k2_zfmisc_1(A_268, B_269))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.74/1.88  tff(c_760, plain, (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', k1_tarski('#skF_3'))=k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_100, c_752])).
% 4.74/1.88  tff(c_764, plain, (k9_relat_1('#skF_6', k1_tarski('#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_409, c_228, c_760])).
% 4.74/1.88  tff(c_64, plain, (![A_45, B_47]: (k9_relat_1(A_45, k1_tarski(B_47))=k11_relat_1(A_45, B_47) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.74/1.88  tff(c_775, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_764, c_64])).
% 4.74/1.88  tff(c_783, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_775])).
% 4.74/1.88  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.74/1.88  tff(c_10, plain, (![A_4, B_5]: (k1_enumset1(A_4, A_4, B_5)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.74/1.88  tff(c_12, plain, (![A_6, B_7, C_8]: (k2_enumset1(A_6, A_6, B_7, C_8)=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.74/1.88  tff(c_191, plain, (![A_122, B_123, C_124, D_125]: (k3_enumset1(A_122, A_122, B_123, C_124, D_125)=k2_enumset1(A_122, B_123, C_124, D_125))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.74/1.88  tff(c_26, plain, (![A_31, G_39, C_33, B_32, E_35]: (r2_hidden(G_39, k3_enumset1(A_31, B_32, C_33, G_39, E_35)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.74/1.88  tff(c_215, plain, (![C_126, A_127, B_128, D_129]: (r2_hidden(C_126, k2_enumset1(A_127, B_128, C_126, D_129)))), inference(superposition, [status(thm), theory('equality')], [c_191, c_26])).
% 4.74/1.88  tff(c_229, plain, (![B_133, A_134, C_135]: (r2_hidden(B_133, k1_enumset1(A_134, B_133, C_135)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_215])).
% 4.74/1.88  tff(c_233, plain, (![A_136, B_137]: (r2_hidden(A_136, k2_tarski(A_136, B_137)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_229])).
% 4.74/1.88  tff(c_236, plain, (![A_3]: (r2_hidden(A_3, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_233])).
% 4.74/1.88  tff(c_1244, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1220, c_236])).
% 4.74/1.88  tff(c_68, plain, (![B_51, A_50]: (k1_tarski(k1_funct_1(B_51, A_50))=k11_relat_1(B_51, A_50) | ~r2_hidden(A_50, k1_relat_1(B_51)) | ~v1_funct_1(B_51) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.74/1.88  tff(c_1254, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1244, c_68])).
% 4.74/1.88  tff(c_1257, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_104, c_783, c_1254])).
% 4.74/1.88  tff(c_96, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 4.74/1.88  tff(c_411, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_409, c_96])).
% 4.74/1.88  tff(c_1351, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1257, c_411])).
% 4.74/1.88  tff(c_1811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1806, c_1351])).
% 4.74/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.74/1.88  
% 4.74/1.88  Inference rules
% 4.74/1.88  ----------------------
% 4.74/1.88  #Ref     : 0
% 4.74/1.88  #Sup     : 379
% 4.74/1.88  #Fact    : 0
% 4.74/1.88  #Define  : 0
% 4.74/1.88  #Split   : 3
% 4.74/1.88  #Chain   : 0
% 4.74/1.88  #Close   : 0
% 4.74/1.88  
% 4.74/1.88  Ordering : KBO
% 4.74/1.88  
% 4.74/1.88  Simplification rules
% 4.74/1.88  ----------------------
% 4.74/1.88  #Subsume      : 38
% 4.74/1.88  #Demod        : 176
% 4.74/1.88  #Tautology    : 145
% 4.74/1.88  #SimpNegUnit  : 4
% 4.74/1.88  #BackRed      : 22
% 4.74/1.88  
% 4.74/1.88  #Partial instantiations: 0
% 4.74/1.88  #Strategies tried      : 1
% 4.74/1.88  
% 4.74/1.88  Timing (in seconds)
% 4.74/1.88  ----------------------
% 4.74/1.88  Preprocessing        : 0.41
% 4.74/1.88  Parsing              : 0.19
% 4.74/1.88  CNF conversion       : 0.03
% 4.74/1.88  Main loop            : 0.67
% 4.74/1.88  Inferencing          : 0.23
% 4.74/1.88  Reduction            : 0.22
% 4.74/1.88  Demodulation         : 0.16
% 4.74/1.88  BG Simplification    : 0.04
% 4.74/1.88  Subsumption          : 0.13
% 4.74/1.88  Abstraction          : 0.04
% 4.74/1.88  MUC search           : 0.00
% 4.74/1.88  Cooper               : 0.00
% 4.74/1.88  Total                : 1.14
% 4.74/1.88  Index Insertion      : 0.00
% 4.74/1.88  Index Deletion       : 0.00
% 4.74/1.88  Index Matching       : 0.00
% 4.74/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
