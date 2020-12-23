%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:20 EST 2020

% Result     : Theorem 5.50s
% Output     : CNFRefutation 5.50s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 148 expanded)
%              Number of leaves         :   37 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  156 ( 407 expanded)
%              Number of equality atoms :   28 (  45 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(A))
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(B))
                       => ( r1_tarski(k7_relset_1(A,B,C,D),E)
                        <=> r1_tarski(D,k8_relset_1(A,B,C,E)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_2)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ! [D] :
          ( v1_relat_1(D)
         => ( ( r1_tarski(C,D)
              & r1_tarski(A,B) )
           => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_86,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_48,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1879,plain,(
    ! [A_279,B_280,C_281,D_282] :
      ( k8_relset_1(A_279,B_280,C_281,D_282) = k10_relat_1(C_281,D_282)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(A_279,B_280))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1886,plain,(
    ! [D_282] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_282) = k10_relat_1('#skF_3',D_282) ),
    inference(resolution,[status(thm)],[c_48,c_1879])).

tff(c_18,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_105,plain,(
    ! [B_72,A_73] :
      ( v1_relat_1(B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_73))
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_111,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_105])).

tff(c_121,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_111])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_528,plain,(
    ! [A_128,B_129,C_130,D_131] :
      ( k8_relset_1(A_128,B_129,C_130,D_131) = k10_relat_1(C_130,D_131)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_535,plain,(
    ! [D_131] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_131) = k10_relat_1('#skF_3',D_131) ),
    inference(resolution,[status(thm)],[c_48,c_528])).

tff(c_58,plain,
    ( ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5'))
    | ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_104,plain,(
    ~ r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,
    ( r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5')
    | r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_139,plain,(
    r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_64])).

tff(c_541,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_139])).

tff(c_861,plain,(
    ! [C_174,A_175,D_176,B_177] :
      ( r1_tarski(k9_relat_1(C_174,A_175),k9_relat_1(D_176,B_177))
      | ~ r1_tarski(A_175,B_177)
      | ~ r1_tarski(C_174,D_176)
      | ~ v1_relat_1(D_176)
      | ~ v1_relat_1(C_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_207,plain,(
    ! [B_83,A_84] :
      ( r1_tarski(k9_relat_1(B_83,k10_relat_1(B_83,A_84)),A_84)
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_226,plain,(
    ! [A_3,A_84,B_83] :
      ( r1_tarski(A_3,A_84)
      | ~ r1_tarski(A_3,k9_relat_1(B_83,k10_relat_1(B_83,A_84)))
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(resolution,[status(thm)],[c_207,c_10])).

tff(c_1482,plain,(
    ! [C_241,A_242,A_243,D_244] :
      ( r1_tarski(k9_relat_1(C_241,A_242),A_243)
      | ~ v1_funct_1(D_244)
      | ~ r1_tarski(A_242,k10_relat_1(D_244,A_243))
      | ~ r1_tarski(C_241,D_244)
      | ~ v1_relat_1(D_244)
      | ~ v1_relat_1(C_241) ) ),
    inference(resolution,[status(thm)],[c_861,c_226])).

tff(c_1503,plain,(
    ! [C_241] :
      ( r1_tarski(k9_relat_1(C_241,'#skF_4'),'#skF_5')
      | ~ v1_funct_1('#skF_3')
      | ~ r1_tarski(C_241,'#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(C_241) ) ),
    inference(resolution,[status(thm)],[c_541,c_1482])).

tff(c_1528,plain,(
    ! [C_245] :
      ( r1_tarski(k9_relat_1(C_245,'#skF_4'),'#skF_5')
      | ~ r1_tarski(C_245,'#skF_3')
      | ~ v1_relat_1(C_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_52,c_1503])).

tff(c_402,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( k7_relset_1(A_104,B_105,C_106,D_107) = k9_relat_1(C_106,D_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_409,plain,(
    ! [D_107] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_107) = k9_relat_1('#skF_3',D_107) ),
    inference(resolution,[status(thm)],[c_48,c_402])).

tff(c_410,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_104])).

tff(c_1536,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1528,c_410])).

tff(c_1556,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_8,c_1536])).

tff(c_1557,plain,(
    ~ r1_tarski('#skF_4',k8_relset_1('#skF_1','#skF_2','#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1887,plain,(
    ~ r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1886,c_1557])).

tff(c_1562,plain,(
    ! [B_246,A_247] :
      ( v1_relat_1(B_246)
      | ~ m1_subset_1(B_246,k1_zfmisc_1(A_247))
      | ~ v1_relat_1(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1568,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_1562])).

tff(c_1578,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1568])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_69,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(A_68,B_69)
      | ~ m1_subset_1(A_68,k1_zfmisc_1(B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_85,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_69])).

tff(c_50,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1756,plain,(
    ! [A_263,B_264,C_265] :
      ( k1_relset_1(A_263,B_264,C_265) = k1_relat_1(C_265)
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_263,B_264))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1765,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1756])).

tff(c_2150,plain,(
    ! [B_326,A_327,C_328] :
      ( k1_xboole_0 = B_326
      | k1_relset_1(A_327,B_326,C_328) = A_327
      | ~ v1_funct_2(C_328,A_327,B_326)
      | ~ m1_subset_1(C_328,k1_zfmisc_1(k2_zfmisc_1(A_327,B_326))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2157,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_2150])).

tff(c_2161,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1765,c_2157])).

tff(c_2162,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2161])).

tff(c_1969,plain,(
    ! [A_301,B_302,C_303,D_304] :
      ( k7_relset_1(A_301,B_302,C_303,D_304) = k9_relat_1(C_303,D_304)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_301,B_302))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1976,plain,(
    ! [D_304] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_304) = k9_relat_1('#skF_3',D_304) ),
    inference(resolution,[status(thm)],[c_48,c_1969])).

tff(c_1558,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1982,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1976,c_1558])).

tff(c_2532,plain,(
    ! [A_373,C_374,B_375] :
      ( r1_tarski(A_373,k10_relat_1(C_374,B_375))
      | ~ r1_tarski(k9_relat_1(C_374,A_373),B_375)
      | ~ r1_tarski(A_373,k1_relat_1(C_374))
      | ~ v1_funct_1(C_374)
      | ~ v1_relat_1(C_374) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2559,plain,
    ( r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_4',k1_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1982,c_2532])).

tff(c_2590,plain,(
    r1_tarski('#skF_4',k10_relat_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1578,c_52,c_85,c_2162,c_2559])).

tff(c_2592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1887,c_2590])).

tff(c_2593,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2161])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2603,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2593,c_2])).

tff(c_2605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2603])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:07:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.50/2.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.50/2.15  
% 5.50/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.50/2.15  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.50/2.15  
% 5.50/2.15  %Foreground sorts:
% 5.50/2.15  
% 5.50/2.15  
% 5.50/2.15  %Background operators:
% 5.50/2.15  
% 5.50/2.15  
% 5.50/2.15  %Foreground operators:
% 5.50/2.15  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.50/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.50/2.15  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 5.50/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.50/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.50/2.15  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.50/2.15  tff('#skF_5', type, '#skF_5': $i).
% 5.50/2.15  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.50/2.15  tff('#skF_2', type, '#skF_2': $i).
% 5.50/2.15  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.50/2.15  tff('#skF_3', type, '#skF_3': $i).
% 5.50/2.15  tff('#skF_1', type, '#skF_1': $i).
% 5.50/2.15  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.50/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.50/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.50/2.15  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.50/2.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.50/2.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.50/2.15  tff('#skF_4', type, '#skF_4': $i).
% 5.50/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.50/2.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.50/2.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.50/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.50/2.15  
% 5.50/2.17  tff(f_133, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (r1_tarski(k7_relset_1(A, B, C, D), E) <=> r1_tarski(D, k8_relset_1(A, B, C, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_2)).
% 5.50/2.17  tff(f_90, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 5.50/2.17  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.50/2.17  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.50/2.17  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.50/2.17  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_relat_1)).
% 5.50/2.17  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 5.50/2.17  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.50/2.17  tff(f_86, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.50/2.17  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.50/2.17  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.50/2.17  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.50/2.17  tff(f_78, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 5.50/2.17  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.50/2.17  tff(c_54, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.50/2.17  tff(c_48, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.50/2.17  tff(c_1879, plain, (![A_279, B_280, C_281, D_282]: (k8_relset_1(A_279, B_280, C_281, D_282)=k10_relat_1(C_281, D_282) | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(A_279, B_280))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.50/2.17  tff(c_1886, plain, (![D_282]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_282)=k10_relat_1('#skF_3', D_282))), inference(resolution, [status(thm)], [c_48, c_1879])).
% 5.50/2.17  tff(c_18, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.50/2.17  tff(c_105, plain, (![B_72, A_73]: (v1_relat_1(B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(A_73)) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.50/2.17  tff(c_111, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_105])).
% 5.50/2.17  tff(c_121, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_111])).
% 5.50/2.17  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.50/2.17  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.50/2.17  tff(c_528, plain, (![A_128, B_129, C_130, D_131]: (k8_relset_1(A_128, B_129, C_130, D_131)=k10_relat_1(C_130, D_131) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.50/2.17  tff(c_535, plain, (![D_131]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_131)=k10_relat_1('#skF_3', D_131))), inference(resolution, [status(thm)], [c_48, c_528])).
% 5.50/2.17  tff(c_58, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')) | ~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.50/2.17  tff(c_104, plain, (~r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_58])).
% 5.50/2.17  tff(c_64, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5') | r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.50/2.17  tff(c_139, plain, (r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_104, c_64])).
% 5.50/2.17  tff(c_541, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_535, c_139])).
% 5.50/2.17  tff(c_861, plain, (![C_174, A_175, D_176, B_177]: (r1_tarski(k9_relat_1(C_174, A_175), k9_relat_1(D_176, B_177)) | ~r1_tarski(A_175, B_177) | ~r1_tarski(C_174, D_176) | ~v1_relat_1(D_176) | ~v1_relat_1(C_174))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.50/2.17  tff(c_207, plain, (![B_83, A_84]: (r1_tarski(k9_relat_1(B_83, k10_relat_1(B_83, A_84)), A_84) | ~v1_funct_1(B_83) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.50/2.17  tff(c_10, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.50/2.17  tff(c_226, plain, (![A_3, A_84, B_83]: (r1_tarski(A_3, A_84) | ~r1_tarski(A_3, k9_relat_1(B_83, k10_relat_1(B_83, A_84))) | ~v1_funct_1(B_83) | ~v1_relat_1(B_83))), inference(resolution, [status(thm)], [c_207, c_10])).
% 5.50/2.17  tff(c_1482, plain, (![C_241, A_242, A_243, D_244]: (r1_tarski(k9_relat_1(C_241, A_242), A_243) | ~v1_funct_1(D_244) | ~r1_tarski(A_242, k10_relat_1(D_244, A_243)) | ~r1_tarski(C_241, D_244) | ~v1_relat_1(D_244) | ~v1_relat_1(C_241))), inference(resolution, [status(thm)], [c_861, c_226])).
% 5.50/2.17  tff(c_1503, plain, (![C_241]: (r1_tarski(k9_relat_1(C_241, '#skF_4'), '#skF_5') | ~v1_funct_1('#skF_3') | ~r1_tarski(C_241, '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(C_241))), inference(resolution, [status(thm)], [c_541, c_1482])).
% 5.50/2.17  tff(c_1528, plain, (![C_245]: (r1_tarski(k9_relat_1(C_245, '#skF_4'), '#skF_5') | ~r1_tarski(C_245, '#skF_3') | ~v1_relat_1(C_245))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_52, c_1503])).
% 5.50/2.17  tff(c_402, plain, (![A_104, B_105, C_106, D_107]: (k7_relset_1(A_104, B_105, C_106, D_107)=k9_relat_1(C_106, D_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.50/2.17  tff(c_409, plain, (![D_107]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_107)=k9_relat_1('#skF_3', D_107))), inference(resolution, [status(thm)], [c_48, c_402])).
% 5.50/2.17  tff(c_410, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_409, c_104])).
% 5.50/2.17  tff(c_1536, plain, (~r1_tarski('#skF_3', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1528, c_410])).
% 5.50/2.17  tff(c_1556, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_8, c_1536])).
% 5.50/2.17  tff(c_1557, plain, (~r1_tarski('#skF_4', k8_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_58])).
% 5.50/2.17  tff(c_1887, plain, (~r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1886, c_1557])).
% 5.50/2.17  tff(c_1562, plain, (![B_246, A_247]: (v1_relat_1(B_246) | ~m1_subset_1(B_246, k1_zfmisc_1(A_247)) | ~v1_relat_1(A_247))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.50/2.17  tff(c_1568, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_1562])).
% 5.50/2.17  tff(c_1578, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1568])).
% 5.50/2.17  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.50/2.17  tff(c_69, plain, (![A_68, B_69]: (r1_tarski(A_68, B_69) | ~m1_subset_1(A_68, k1_zfmisc_1(B_69)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.50/2.17  tff(c_85, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_69])).
% 5.50/2.17  tff(c_50, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.50/2.17  tff(c_1756, plain, (![A_263, B_264, C_265]: (k1_relset_1(A_263, B_264, C_265)=k1_relat_1(C_265) | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(A_263, B_264))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.50/2.17  tff(c_1765, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1756])).
% 5.50/2.17  tff(c_2150, plain, (![B_326, A_327, C_328]: (k1_xboole_0=B_326 | k1_relset_1(A_327, B_326, C_328)=A_327 | ~v1_funct_2(C_328, A_327, B_326) | ~m1_subset_1(C_328, k1_zfmisc_1(k2_zfmisc_1(A_327, B_326))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.50/2.17  tff(c_2157, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_2150])).
% 5.50/2.17  tff(c_2161, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1765, c_2157])).
% 5.50/2.17  tff(c_2162, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_2161])).
% 5.50/2.17  tff(c_1969, plain, (![A_301, B_302, C_303, D_304]: (k7_relset_1(A_301, B_302, C_303, D_304)=k9_relat_1(C_303, D_304) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_301, B_302))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.50/2.17  tff(c_1976, plain, (![D_304]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_304)=k9_relat_1('#skF_3', D_304))), inference(resolution, [status(thm)], [c_48, c_1969])).
% 5.50/2.17  tff(c_1558, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_58])).
% 5.50/2.17  tff(c_1982, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1976, c_1558])).
% 5.50/2.17  tff(c_2532, plain, (![A_373, C_374, B_375]: (r1_tarski(A_373, k10_relat_1(C_374, B_375)) | ~r1_tarski(k9_relat_1(C_374, A_373), B_375) | ~r1_tarski(A_373, k1_relat_1(C_374)) | ~v1_funct_1(C_374) | ~v1_relat_1(C_374))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.50/2.17  tff(c_2559, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1982, c_2532])).
% 5.50/2.17  tff(c_2590, plain, (r1_tarski('#skF_4', k10_relat_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1578, c_52, c_85, c_2162, c_2559])).
% 5.50/2.17  tff(c_2592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1887, c_2590])).
% 5.50/2.17  tff(c_2593, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2161])).
% 5.50/2.17  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.50/2.17  tff(c_2603, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2593, c_2])).
% 5.50/2.17  tff(c_2605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_2603])).
% 5.50/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.50/2.17  
% 5.50/2.17  Inference rules
% 5.50/2.17  ----------------------
% 5.50/2.17  #Ref     : 0
% 5.90/2.17  #Sup     : 569
% 5.90/2.17  #Fact    : 0
% 5.90/2.17  #Define  : 0
% 5.90/2.17  #Split   : 30
% 5.90/2.17  #Chain   : 0
% 5.90/2.17  #Close   : 0
% 5.90/2.17  
% 5.90/2.17  Ordering : KBO
% 5.90/2.17  
% 5.90/2.17  Simplification rules
% 5.90/2.17  ----------------------
% 5.90/2.17  #Subsume      : 142
% 5.90/2.17  #Demod        : 262
% 5.90/2.17  #Tautology    : 91
% 5.90/2.17  #SimpNegUnit  : 20
% 5.90/2.17  #BackRed      : 56
% 5.90/2.17  
% 5.90/2.17  #Partial instantiations: 0
% 5.90/2.17  #Strategies tried      : 1
% 5.90/2.17  
% 5.90/2.17  Timing (in seconds)
% 5.90/2.17  ----------------------
% 5.90/2.17  Preprocessing        : 0.37
% 5.90/2.17  Parsing              : 0.19
% 5.90/2.17  CNF conversion       : 0.03
% 5.90/2.17  Main loop            : 0.96
% 5.90/2.17  Inferencing          : 0.33
% 5.90/2.17  Reduction            : 0.30
% 5.90/2.17  Demodulation         : 0.21
% 5.90/2.17  BG Simplification    : 0.04
% 5.90/2.17  Subsumption          : 0.23
% 5.90/2.17  Abstraction          : 0.05
% 5.90/2.17  MUC search           : 0.00
% 5.90/2.17  Cooper               : 0.00
% 5.90/2.17  Total                : 1.37
% 5.90/2.17  Index Insertion      : 0.00
% 5.90/2.17  Index Deletion       : 0.00
% 5.90/2.17  Index Matching       : 0.00
% 5.90/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
