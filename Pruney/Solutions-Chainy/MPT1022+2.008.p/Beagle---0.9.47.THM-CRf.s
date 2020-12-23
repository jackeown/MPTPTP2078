%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:14 EST 2020

% Result     : Theorem 5.15s
% Output     : CNFRefutation 5.46s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 732 expanded)
%              Number of leaves         :   52 ( 268 expanded)
%              Depth                    :   16
%              Number of atoms          :  402 (1957 expanded)
%              Number of equality atoms :  107 ( 442 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_169,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_116,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_128,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_146,axiom,(
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
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_154,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(c_86,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_3564,plain,(
    ! [A_532,B_533,C_534,D_535] :
      ( k8_relset_1(A_532,B_533,C_534,D_535) = k10_relat_1(C_534,D_535)
      | ~ m1_subset_1(C_534,k1_zfmisc_1(k2_zfmisc_1(A_532,B_533))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3567,plain,(
    ! [D_535] : k8_relset_1('#skF_4','#skF_4','#skF_6',D_535) = k10_relat_1('#skF_6',D_535) ),
    inference(resolution,[status(thm)],[c_86,c_3564])).

tff(c_3521,plain,(
    ! [A_524,B_525,C_526,D_527] :
      ( k7_relset_1(A_524,B_525,C_526,D_527) = k9_relat_1(C_526,D_527)
      | ~ m1_subset_1(C_526,k1_zfmisc_1(k2_zfmisc_1(A_524,B_525))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3524,plain,(
    ! [D_527] : k7_relset_1('#skF_4','#skF_4','#skF_6',D_527) = k9_relat_1('#skF_6',D_527) ),
    inference(resolution,[status(thm)],[c_86,c_3521])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_20,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1030,plain,(
    ! [B_221,A_222] :
      ( v1_relat_1(B_221)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(A_222))
      | ~ v1_relat_1(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1033,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_86,c_1030])).

tff(c_1036,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1033])).

tff(c_92,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_88,plain,(
    v3_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1822,plain,(
    ! [C_338,A_339,B_340] :
      ( v2_funct_1(C_338)
      | ~ v3_funct_2(C_338,A_339,B_340)
      | ~ v1_funct_1(C_338)
      | ~ m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(A_339,B_340))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1825,plain,
    ( v2_funct_1('#skF_6')
    | ~ v3_funct_2('#skF_6','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_1822])).

tff(c_1828,plain,(
    v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_1825])).

tff(c_90,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_1365,plain,(
    ! [A_291,B_292,C_293] :
      ( k1_relset_1(A_291,B_292,C_293) = k1_relat_1(C_293)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(A_291,B_292))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1369,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_1365])).

tff(c_2322,plain,(
    ! [B_392,A_393,C_394] :
      ( k1_xboole_0 = B_392
      | k1_relset_1(A_393,B_392,C_394) = A_393
      | ~ v1_funct_2(C_394,A_393,B_392)
      | ~ m1_subset_1(C_394,k1_zfmisc_1(k2_zfmisc_1(A_393,B_392))) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2325,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_4','#skF_4','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_2322])).

tff(c_2328,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1369,c_2325])).

tff(c_2329,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2328])).

tff(c_84,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1087,plain,(
    ! [C_231,B_232,A_233] :
      ( r2_hidden(C_231,B_232)
      | ~ r2_hidden(C_231,A_233)
      | ~ r1_tarski(A_233,B_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1388,plain,(
    ! [A_295,B_296,B_297] :
      ( r2_hidden('#skF_1'(A_295,B_296),B_297)
      | ~ r1_tarski(A_295,B_297)
      | r1_tarski(A_295,B_296) ) ),
    inference(resolution,[status(thm)],[c_6,c_1087])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1889,plain,(
    ! [A_350,B_351,B_352,B_353] :
      ( r2_hidden('#skF_1'(A_350,B_351),B_352)
      | ~ r1_tarski(B_353,B_352)
      | ~ r1_tarski(A_350,B_353)
      | r1_tarski(A_350,B_351) ) ),
    inference(resolution,[status(thm)],[c_1388,c_2])).

tff(c_1902,plain,(
    ! [A_354,B_355] :
      ( r2_hidden('#skF_1'(A_354,B_355),'#skF_4')
      | ~ r1_tarski(A_354,'#skF_5')
      | r1_tarski(A_354,B_355) ) ),
    inference(resolution,[status(thm)],[c_84,c_1889])).

tff(c_1929,plain,(
    ! [A_359,B_360,B_361] :
      ( r2_hidden('#skF_1'(A_359,B_360),B_361)
      | ~ r1_tarski('#skF_4',B_361)
      | ~ r1_tarski(A_359,'#skF_5')
      | r1_tarski(A_359,B_360) ) ),
    inference(resolution,[status(thm)],[c_1902,c_2])).

tff(c_1096,plain,(
    ! [C_237,B_238,A_239] :
      ( v5_relat_1(C_237,B_238)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_239,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1100,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_1096])).

tff(c_1106,plain,(
    ! [B_241,A_242] :
      ( k2_relat_1(B_241) = A_242
      | ~ v2_funct_2(B_241,A_242)
      | ~ v5_relat_1(B_241,A_242)
      | ~ v1_relat_1(B_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1109,plain,
    ( k2_relat_1('#skF_6') = '#skF_4'
    | ~ v2_funct_2('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1100,c_1106])).

tff(c_1112,plain,
    ( k2_relat_1('#skF_6') = '#skF_4'
    | ~ v2_funct_2('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1036,c_1109])).

tff(c_1113,plain,(
    ~ v2_funct_2('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1112])).

tff(c_1316,plain,(
    ! [C_286,B_287,A_288] :
      ( v2_funct_2(C_286,B_287)
      | ~ v3_funct_2(C_286,A_288,B_287)
      | ~ v1_funct_1(C_286)
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(A_288,B_287))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1319,plain,
    ( v2_funct_2('#skF_6','#skF_4')
    | ~ v3_funct_2('#skF_6','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_1316])).

tff(c_1322,plain,(
    v2_funct_2('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_1319])).

tff(c_1324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1113,c_1322])).

tff(c_1325,plain,(
    k2_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1112])).

tff(c_24,plain,(
    ! [A_18] :
      ( k10_relat_1(A_18,k2_relat_1(A_18)) = k1_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1333,plain,
    ( k10_relat_1('#skF_6','#skF_4') = k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1325,c_24])).

tff(c_1339,plain,(
    k10_relat_1('#skF_6','#skF_4') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1036,c_1333])).

tff(c_1634,plain,(
    ! [A_321,D_322,B_323] :
      ( r2_hidden(k1_funct_1(A_321,D_322),B_323)
      | ~ r2_hidden(D_322,k10_relat_1(A_321,B_323))
      | ~ v1_funct_1(A_321)
      | ~ v1_relat_1(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_48,plain,(
    ! [B_36,A_35] :
      ( ~ r1_tarski(B_36,A_35)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1829,plain,(
    ! [B_341,A_342,D_343] :
      ( ~ r1_tarski(B_341,k1_funct_1(A_342,D_343))
      | ~ r2_hidden(D_343,k10_relat_1(A_342,B_341))
      | ~ v1_funct_1(A_342)
      | ~ v1_relat_1(A_342) ) ),
    inference(resolution,[status(thm)],[c_1634,c_48])).

tff(c_1846,plain,(
    ! [D_343] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_6',D_343))
      | ~ r2_hidden(D_343,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1339,c_1829])).

tff(c_1859,plain,(
    ! [D_343] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_6',D_343))
      | ~ r2_hidden(D_343,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1036,c_92,c_1846])).

tff(c_1955,plain,(
    ! [A_359,B_360] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_6','#skF_1'(A_359,B_360)))
      | ~ r1_tarski('#skF_4',k1_relat_1('#skF_6'))
      | ~ r1_tarski(A_359,'#skF_5')
      | r1_tarski(A_359,B_360) ) ),
    inference(resolution,[status(thm)],[c_1929,c_1859])).

tff(c_2003,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1955])).

tff(c_2333,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2329,c_2003])).

tff(c_2349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2333])).

tff(c_2350,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2328])).

tff(c_16,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1968,plain,(
    ! [B_366,A_367,B_368] :
      ( ~ r1_tarski(B_366,'#skF_1'(A_367,B_368))
      | ~ r1_tarski('#skF_4',B_366)
      | ~ r1_tarski(A_367,'#skF_5')
      | r1_tarski(A_367,B_368) ) ),
    inference(resolution,[status(thm)],[c_1929,c_48])).

tff(c_1978,plain,(
    ! [A_367,B_368] :
      ( ~ r1_tarski('#skF_4',k1_xboole_0)
      | ~ r1_tarski(A_367,'#skF_5')
      | r1_tarski(A_367,B_368) ) ),
    inference(resolution,[status(thm)],[c_16,c_1968])).

tff(c_1980,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1978])).

tff(c_2359,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2350,c_1980])).

tff(c_2371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2359])).

tff(c_2373,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1955])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1960,plain,(
    ! [B_361,A_359] :
      ( ~ r1_tarski('#skF_4',B_361)
      | ~ r1_tarski(A_359,'#skF_5')
      | r1_tarski(A_359,B_361) ) ),
    inference(resolution,[status(thm)],[c_1929,c_4])).

tff(c_2401,plain,(
    ! [A_359] :
      ( ~ r1_tarski(A_359,'#skF_5')
      | r1_tarski(A_359,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_2373,c_1960])).

tff(c_2591,plain,(
    ! [B_407,A_408] :
      ( k10_relat_1(B_407,k9_relat_1(B_407,A_408)) = A_408
      | ~ v2_funct_1(B_407)
      | ~ r1_tarski(A_408,k1_relat_1(B_407))
      | ~ v1_funct_1(B_407)
      | ~ v1_relat_1(B_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2593,plain,(
    ! [A_359] :
      ( k10_relat_1('#skF_6',k9_relat_1('#skF_6',A_359)) = A_359
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r1_tarski(A_359,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2401,c_2591])).

tff(c_2705,plain,(
    ! [A_416] :
      ( k10_relat_1('#skF_6',k9_relat_1('#skF_6',A_416)) = A_416
      | ~ r1_tarski(A_416,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1036,c_92,c_1828,c_2593])).

tff(c_1777,plain,(
    ! [A_331,B_332,C_333,D_334] :
      ( k8_relset_1(A_331,B_332,C_333,D_334) = k10_relat_1(C_333,D_334)
      | ~ m1_subset_1(C_333,k1_zfmisc_1(k2_zfmisc_1(A_331,B_332))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1780,plain,(
    ! [D_334] : k8_relset_1('#skF_4','#skF_4','#skF_6',D_334) = k10_relat_1('#skF_6',D_334) ),
    inference(resolution,[status(thm)],[c_86,c_1777])).

tff(c_1511,plain,(
    ! [A_311,B_312,C_313,D_314] :
      ( k7_relset_1(A_311,B_312,C_313,D_314) = k9_relat_1(C_313,D_314)
      | ~ m1_subset_1(C_313,k1_zfmisc_1(k2_zfmisc_1(A_311,B_312))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1514,plain,(
    ! [D_314] : k7_relset_1('#skF_4','#skF_4','#skF_6',D_314) = k9_relat_1('#skF_6',D_314) ),
    inference(resolution,[status(thm)],[c_86,c_1511])).

tff(c_142,plain,(
    ! [B_69,A_70] :
      ( v1_relat_1(B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70))
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_145,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_86,c_142])).

tff(c_148,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_145])).

tff(c_213,plain,(
    ! [C_87,B_88,A_89] :
      ( v5_relat_1(C_87,B_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_217,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_213])).

tff(c_233,plain,(
    ! [B_93,A_94] :
      ( k2_relat_1(B_93) = A_94
      | ~ v2_funct_2(B_93,A_94)
      | ~ v5_relat_1(B_93,A_94)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_236,plain,
    ( k2_relat_1('#skF_6') = '#skF_4'
    | ~ v2_funct_2('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_217,c_233])).

tff(c_239,plain,
    ( k2_relat_1('#skF_6') = '#skF_4'
    | ~ v2_funct_2('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_236])).

tff(c_240,plain,(
    ~ v2_funct_2('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_492,plain,(
    ! [C_157,B_158,A_159] :
      ( v2_funct_2(C_157,B_158)
      | ~ v3_funct_2(C_157,A_159,B_158)
      | ~ v1_funct_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_159,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_495,plain,
    ( v2_funct_2('#skF_6','#skF_4')
    | ~ v3_funct_2('#skF_6','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_492])).

tff(c_498,plain,(
    v2_funct_2('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_495])).

tff(c_500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_498])).

tff(c_501,plain,(
    k2_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_789,plain,(
    ! [B_188,A_189] :
      ( k9_relat_1(B_188,k10_relat_1(B_188,A_189)) = A_189
      | ~ r1_tarski(A_189,k2_relat_1(B_188))
      | ~ v1_funct_1(B_188)
      | ~ v1_relat_1(B_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_791,plain,(
    ! [A_189] :
      ( k9_relat_1('#skF_6',k10_relat_1('#skF_6',A_189)) = A_189
      | ~ r1_tarski(A_189,'#skF_4')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_789])).

tff(c_799,plain,(
    ! [A_189] :
      ( k9_relat_1('#skF_6',k10_relat_1('#skF_6',A_189)) = A_189
      | ~ r1_tarski(A_189,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_92,c_791])).

tff(c_958,plain,(
    ! [A_208,B_209,C_210,D_211] :
      ( k7_relset_1(A_208,B_209,C_210,D_211) = k9_relat_1(C_210,D_211)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_961,plain,(
    ! [D_211] : k7_relset_1('#skF_4','#skF_4','#skF_6',D_211) = k9_relat_1('#skF_6',D_211) ),
    inference(resolution,[status(thm)],[c_86,c_958])).

tff(c_943,plain,(
    ! [A_201,B_202,C_203,D_204] :
      ( k8_relset_1(A_201,B_202,C_203,D_204) = k10_relat_1(C_203,D_204)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(k2_zfmisc_1(A_201,B_202))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_946,plain,(
    ! [D_204] : k8_relset_1('#skF_4','#skF_4','#skF_6',D_204) = k10_relat_1('#skF_6',D_204) ),
    inference(resolution,[status(thm)],[c_86,c_943])).

tff(c_82,plain,
    ( k8_relset_1('#skF_4','#skF_4','#skF_6',k7_relset_1('#skF_4','#skF_4','#skF_6','#skF_5')) != '#skF_5'
    | k7_relset_1('#skF_4','#skF_4','#skF_6',k8_relset_1('#skF_4','#skF_4','#skF_6','#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_98,plain,(
    k7_relset_1('#skF_4','#skF_4','#skF_6',k8_relset_1('#skF_4','#skF_4','#skF_6','#skF_5')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_947,plain,(
    k7_relset_1('#skF_4','#skF_4','#skF_6',k10_relat_1('#skF_6','#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_946,c_98])).

tff(c_963,plain,(
    k9_relat_1('#skF_6',k10_relat_1('#skF_6','#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_961,c_947])).

tff(c_975,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_799,c_963])).

tff(c_979,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_975])).

tff(c_980,plain,(
    k8_relset_1('#skF_4','#skF_4','#skF_6',k7_relset_1('#skF_4','#skF_4','#skF_6','#skF_5')) != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_1541,plain,(
    k8_relset_1('#skF_4','#skF_4','#skF_6',k9_relat_1('#skF_6','#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1514,c_980])).

tff(c_1783,plain,(
    k10_relat_1('#skF_6',k9_relat_1('#skF_6','#skF_5')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1780,c_1541])).

tff(c_2720,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2705,c_1783])).

tff(c_2778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2720])).

tff(c_2780,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1978])).

tff(c_1402,plain,(
    ! [B_299,A_300,B_301] :
      ( ~ r1_tarski(B_299,'#skF_1'(A_300,B_301))
      | ~ r1_tarski(A_300,B_299)
      | r1_tarski(A_300,B_301) ) ),
    inference(resolution,[status(thm)],[c_1388,c_48])).

tff(c_1412,plain,(
    ! [A_300,B_301] :
      ( ~ r1_tarski(A_300,k1_xboole_0)
      | r1_tarski(A_300,B_301) ) ),
    inference(resolution,[status(thm)],[c_16,c_1402])).

tff(c_2804,plain,(
    ! [B_301] : r1_tarski('#skF_4',B_301) ),
    inference(resolution,[status(thm)],[c_2780,c_1412])).

tff(c_1053,plain,(
    ! [B_226,A_227] :
      ( B_226 = A_227
      | ~ r1_tarski(B_226,A_227)
      | ~ r1_tarski(A_227,B_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1065,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_1053])).

tff(c_1079,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1065])).

tff(c_2843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2804,c_1079])).

tff(c_2844,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1065])).

tff(c_2876,plain,(
    k8_relset_1('#skF_4','#skF_4','#skF_6',k7_relset_1('#skF_4','#skF_4','#skF_6','#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2844,c_2844,c_980])).

tff(c_3543,plain,(
    k8_relset_1('#skF_4','#skF_4','#skF_6',k9_relat_1('#skF_6','#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3524,c_2876])).

tff(c_3569,plain,(
    k10_relat_1('#skF_6',k9_relat_1('#skF_6','#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3567,c_3543])).

tff(c_3201,plain,(
    ! [A_500,B_501,C_502] :
      ( k1_relset_1(A_500,B_501,C_502) = k1_relat_1(C_502)
      | ~ m1_subset_1(C_502,k1_zfmisc_1(k2_zfmisc_1(A_500,B_501))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_3205,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_3201])).

tff(c_4010,plain,(
    ! [B_574,A_575,C_576] :
      ( k1_xboole_0 = B_574
      | k1_relset_1(A_575,B_574,C_576) = A_575
      | ~ v1_funct_2(C_576,A_575,B_574)
      | ~ m1_subset_1(C_576,k1_zfmisc_1(k2_zfmisc_1(A_575,B_574))) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_4013,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_4','#skF_4','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_4010])).

tff(c_4016,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_3205,c_4013])).

tff(c_4017,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4016])).

tff(c_2871,plain,(
    ! [C_428,B_429,A_430] :
      ( v5_relat_1(C_428,B_429)
      | ~ m1_subset_1(C_428,k1_zfmisc_1(k2_zfmisc_1(A_430,B_429))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2875,plain,(
    v5_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_2871])).

tff(c_2883,plain,(
    ! [B_432,A_433] :
      ( k2_relat_1(B_432) = A_433
      | ~ v2_funct_2(B_432,A_433)
      | ~ v5_relat_1(B_432,A_433)
      | ~ v1_relat_1(B_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_2886,plain,
    ( k2_relat_1('#skF_6') = '#skF_4'
    | ~ v2_funct_2('#skF_6','#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2875,c_2883])).

tff(c_2889,plain,
    ( k2_relat_1('#skF_6') = '#skF_4'
    | ~ v2_funct_2('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1036,c_2886])).

tff(c_2890,plain,(
    ~ v2_funct_2('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2889])).

tff(c_3102,plain,(
    ! [C_485,B_486,A_487] :
      ( v2_funct_2(C_485,B_486)
      | ~ v3_funct_2(C_485,A_487,B_486)
      | ~ v1_funct_1(C_485)
      | ~ m1_subset_1(C_485,k1_zfmisc_1(k2_zfmisc_1(A_487,B_486))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_3105,plain,
    ( v2_funct_2('#skF_6','#skF_4')
    | ~ v3_funct_2('#skF_6','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_3102])).

tff(c_3108,plain,(
    v2_funct_2('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_3105])).

tff(c_3110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2890,c_3108])).

tff(c_3111,plain,(
    k2_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2889])).

tff(c_3136,plain,
    ( k10_relat_1('#skF_6','#skF_4') = k1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3111,c_24])).

tff(c_3144,plain,(
    k10_relat_1('#skF_6','#skF_4') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1036,c_3136])).

tff(c_4034,plain,(
    k10_relat_1('#skF_6','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4017,c_3144])).

tff(c_3396,plain,(
    ! [B_517,A_518] :
      ( k9_relat_1(B_517,k10_relat_1(B_517,A_518)) = A_518
      | ~ r1_tarski(A_518,k2_relat_1(B_517))
      | ~ v1_funct_1(B_517)
      | ~ v1_relat_1(B_517) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3473,plain,(
    ! [B_522] :
      ( k9_relat_1(B_522,k10_relat_1(B_522,k2_relat_1(B_522))) = k2_relat_1(B_522)
      | ~ v1_funct_1(B_522)
      | ~ v1_relat_1(B_522) ) ),
    inference(resolution,[status(thm)],[c_12,c_3396])).

tff(c_3493,plain,(
    ! [A_18] :
      ( k9_relat_1(A_18,k1_relat_1(A_18)) = k2_relat_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_3473])).

tff(c_4040,plain,
    ( k9_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4017,c_3493])).

tff(c_4046,plain,(
    k9_relat_1('#skF_6','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1036,c_1036,c_92,c_3111,c_4040])).

tff(c_4052,plain,(
    k10_relat_1('#skF_6','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4046,c_3569])).

tff(c_4085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4034,c_4052])).

tff(c_4086,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4016])).

tff(c_3582,plain,(
    ! [C_537,A_538,B_539] :
      ( v2_funct_1(C_537)
      | ~ v3_funct_2(C_537,A_538,B_539)
      | ~ v1_funct_1(C_537)
      | ~ m1_subset_1(C_537,k1_zfmisc_1(k2_zfmisc_1(A_538,B_539))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_3585,plain,
    ( v2_funct_1('#skF_6')
    | ~ v3_funct_2('#skF_6','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_86,c_3582])).

tff(c_3588,plain,(
    v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_3585])).

tff(c_982,plain,(
    ! [A_215,B_216] :
      ( k3_xboole_0(A_215,B_216) = A_215
      | ~ r1_tarski(A_215,B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_993,plain,(
    ! [A_10] : k3_xboole_0(k1_xboole_0,A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_982])).

tff(c_3711,plain,(
    ! [B_565,A_566] :
      ( k10_relat_1(B_565,k9_relat_1(B_565,A_566)) = A_566
      | ~ v2_funct_1(B_565)
      | ~ r1_tarski(A_566,k1_relat_1(B_565))
      | ~ v1_funct_1(B_565)
      | ~ v1_relat_1(B_565) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3845,plain,(
    ! [B_571] :
      ( k10_relat_1(B_571,k9_relat_1(B_571,k1_xboole_0)) = k1_xboole_0
      | ~ v2_funct_1(B_571)
      | ~ v1_funct_1(B_571)
      | ~ v1_relat_1(B_571) ) ),
    inference(resolution,[status(thm)],[c_16,c_3711])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( k10_relat_1(B_17,k3_xboole_0(k2_relat_1(B_17),A_16)) = k10_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3130,plain,(
    ! [A_16] :
      ( k10_relat_1('#skF_6',k3_xboole_0('#skF_4',A_16)) = k10_relat_1('#skF_6',A_16)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3111,c_22])).

tff(c_3140,plain,(
    ! [A_16] : k10_relat_1('#skF_6',k3_xboole_0('#skF_4',A_16)) = k10_relat_1('#skF_6',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1036,c_3130])).

tff(c_3210,plain,(
    ! [D_503,A_504,B_505] :
      ( r2_hidden(D_503,k1_relat_1(A_504))
      | ~ r2_hidden(D_503,k10_relat_1(A_504,B_505))
      | ~ v1_funct_1(A_504)
      | ~ v1_relat_1(A_504) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3217,plain,(
    ! [D_503,A_16] :
      ( r2_hidden(D_503,k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_503,k10_relat_1('#skF_6',A_16))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3140,c_3210])).

tff(c_3237,plain,(
    ! [D_506,A_507] :
      ( r2_hidden(D_506,k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_506,k10_relat_1('#skF_6',A_507)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1036,c_92,c_3217])).

tff(c_3264,plain,(
    ! [A_508,B_509] :
      ( r2_hidden('#skF_1'(k10_relat_1('#skF_6',A_508),B_509),k1_relat_1('#skF_6'))
      | r1_tarski(k10_relat_1('#skF_6',A_508),B_509) ) ),
    inference(resolution,[status(thm)],[c_6,c_3237])).

tff(c_3297,plain,(
    ! [A_510] : r1_tarski(k10_relat_1('#skF_6',A_510),k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_3264,c_4])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3316,plain,(
    ! [A_510] : k3_xboole_0(k10_relat_1('#skF_6',A_510),k1_relat_1('#skF_6')) = k10_relat_1('#skF_6',A_510) ),
    inference(resolution,[status(thm)],[c_3297,c_14])).

tff(c_3881,plain,
    ( k3_xboole_0(k1_xboole_0,k1_relat_1('#skF_6')) = k10_relat_1('#skF_6',k9_relat_1('#skF_6',k1_xboole_0))
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3845,c_3316])).

tff(c_3918,plain,(
    k10_relat_1('#skF_6',k9_relat_1('#skF_6',k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1036,c_92,c_3588,c_993,c_3881])).

tff(c_4092,plain,(
    k10_relat_1('#skF_6',k9_relat_1('#skF_6','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4086,c_4086,c_3918])).

tff(c_4104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3569,c_4092])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:43:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.15/2.01  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.15/2.03  
% 5.15/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.15/2.03  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.15/2.03  
% 5.15/2.03  %Foreground sorts:
% 5.15/2.03  
% 5.15/2.03  
% 5.15/2.03  %Background operators:
% 5.15/2.03  
% 5.15/2.03  
% 5.15/2.03  %Foreground operators:
% 5.15/2.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.15/2.03  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.15/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.15/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.15/2.03  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 5.15/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.15/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.15/2.03  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.15/2.03  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.15/2.03  tff('#skF_5', type, '#skF_5': $i).
% 5.15/2.03  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.15/2.03  tff('#skF_6', type, '#skF_6': $i).
% 5.15/2.03  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.15/2.03  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.15/2.03  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 5.15/2.03  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.15/2.03  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.15/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.15/2.03  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.15/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.15/2.03  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.15/2.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.15/2.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.15/2.03  tff('#skF_4', type, '#skF_4': $i).
% 5.15/2.03  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.15/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.15/2.03  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.15/2.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.15/2.03  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 5.15/2.03  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.15/2.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.15/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.15/2.03  
% 5.46/2.06  tff(f_169, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_funct_2)).
% 5.46/2.06  tff(f_116, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 5.46/2.06  tff(f_112, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.46/2.06  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.46/2.06  tff(f_53, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.46/2.06  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.46/2.06  tff(f_128, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 5.46/2.06  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.46/2.06  tff(f_146, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.46/2.06  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.46/2.06  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.46/2.06  tff(f_154, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 5.46/2.06  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 5.46/2.06  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 5.46/2.06  tff(f_98, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.46/2.06  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.46/2.06  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 5.46/2.06  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 5.46/2.06  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.46/2.06  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 5.46/2.06  tff(c_86, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.46/2.06  tff(c_3564, plain, (![A_532, B_533, C_534, D_535]: (k8_relset_1(A_532, B_533, C_534, D_535)=k10_relat_1(C_534, D_535) | ~m1_subset_1(C_534, k1_zfmisc_1(k2_zfmisc_1(A_532, B_533))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.46/2.06  tff(c_3567, plain, (![D_535]: (k8_relset_1('#skF_4', '#skF_4', '#skF_6', D_535)=k10_relat_1('#skF_6', D_535))), inference(resolution, [status(thm)], [c_86, c_3564])).
% 5.46/2.06  tff(c_3521, plain, (![A_524, B_525, C_526, D_527]: (k7_relset_1(A_524, B_525, C_526, D_527)=k9_relat_1(C_526, D_527) | ~m1_subset_1(C_526, k1_zfmisc_1(k2_zfmisc_1(A_524, B_525))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.46/2.06  tff(c_3524, plain, (![D_527]: (k7_relset_1('#skF_4', '#skF_4', '#skF_6', D_527)=k9_relat_1('#skF_6', D_527))), inference(resolution, [status(thm)], [c_86, c_3521])).
% 5.46/2.06  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.46/2.06  tff(c_20, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.46/2.06  tff(c_1030, plain, (![B_221, A_222]: (v1_relat_1(B_221) | ~m1_subset_1(B_221, k1_zfmisc_1(A_222)) | ~v1_relat_1(A_222))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.46/2.06  tff(c_1033, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_86, c_1030])).
% 5.46/2.06  tff(c_1036, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1033])).
% 5.46/2.06  tff(c_92, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.46/2.06  tff(c_88, plain, (v3_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.46/2.06  tff(c_1822, plain, (![C_338, A_339, B_340]: (v2_funct_1(C_338) | ~v3_funct_2(C_338, A_339, B_340) | ~v1_funct_1(C_338) | ~m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(A_339, B_340))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.46/2.06  tff(c_1825, plain, (v2_funct_1('#skF_6') | ~v3_funct_2('#skF_6', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_86, c_1822])).
% 5.46/2.06  tff(c_1828, plain, (v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_1825])).
% 5.46/2.06  tff(c_90, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.46/2.06  tff(c_1365, plain, (![A_291, B_292, C_293]: (k1_relset_1(A_291, B_292, C_293)=k1_relat_1(C_293) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(A_291, B_292))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.46/2.06  tff(c_1369, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_86, c_1365])).
% 5.46/2.06  tff(c_2322, plain, (![B_392, A_393, C_394]: (k1_xboole_0=B_392 | k1_relset_1(A_393, B_392, C_394)=A_393 | ~v1_funct_2(C_394, A_393, B_392) | ~m1_subset_1(C_394, k1_zfmisc_1(k2_zfmisc_1(A_393, B_392))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.46/2.06  tff(c_2325, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_4', '#skF_4', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_86, c_2322])).
% 5.46/2.06  tff(c_2328, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1369, c_2325])).
% 5.46/2.06  tff(c_2329, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_2328])).
% 5.46/2.06  tff(c_84, plain, (r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.46/2.06  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.46/2.06  tff(c_1087, plain, (![C_231, B_232, A_233]: (r2_hidden(C_231, B_232) | ~r2_hidden(C_231, A_233) | ~r1_tarski(A_233, B_232))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.46/2.06  tff(c_1388, plain, (![A_295, B_296, B_297]: (r2_hidden('#skF_1'(A_295, B_296), B_297) | ~r1_tarski(A_295, B_297) | r1_tarski(A_295, B_296))), inference(resolution, [status(thm)], [c_6, c_1087])).
% 5.46/2.06  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.46/2.06  tff(c_1889, plain, (![A_350, B_351, B_352, B_353]: (r2_hidden('#skF_1'(A_350, B_351), B_352) | ~r1_tarski(B_353, B_352) | ~r1_tarski(A_350, B_353) | r1_tarski(A_350, B_351))), inference(resolution, [status(thm)], [c_1388, c_2])).
% 5.46/2.06  tff(c_1902, plain, (![A_354, B_355]: (r2_hidden('#skF_1'(A_354, B_355), '#skF_4') | ~r1_tarski(A_354, '#skF_5') | r1_tarski(A_354, B_355))), inference(resolution, [status(thm)], [c_84, c_1889])).
% 5.46/2.06  tff(c_1929, plain, (![A_359, B_360, B_361]: (r2_hidden('#skF_1'(A_359, B_360), B_361) | ~r1_tarski('#skF_4', B_361) | ~r1_tarski(A_359, '#skF_5') | r1_tarski(A_359, B_360))), inference(resolution, [status(thm)], [c_1902, c_2])).
% 5.46/2.06  tff(c_1096, plain, (![C_237, B_238, A_239]: (v5_relat_1(C_237, B_238) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_239, B_238))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.46/2.06  tff(c_1100, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_86, c_1096])).
% 5.46/2.06  tff(c_1106, plain, (![B_241, A_242]: (k2_relat_1(B_241)=A_242 | ~v2_funct_2(B_241, A_242) | ~v5_relat_1(B_241, A_242) | ~v1_relat_1(B_241))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.46/2.06  tff(c_1109, plain, (k2_relat_1('#skF_6')='#skF_4' | ~v2_funct_2('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1100, c_1106])).
% 5.46/2.06  tff(c_1112, plain, (k2_relat_1('#skF_6')='#skF_4' | ~v2_funct_2('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1036, c_1109])).
% 5.46/2.06  tff(c_1113, plain, (~v2_funct_2('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_1112])).
% 5.46/2.06  tff(c_1316, plain, (![C_286, B_287, A_288]: (v2_funct_2(C_286, B_287) | ~v3_funct_2(C_286, A_288, B_287) | ~v1_funct_1(C_286) | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(A_288, B_287))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.46/2.06  tff(c_1319, plain, (v2_funct_2('#skF_6', '#skF_4') | ~v3_funct_2('#skF_6', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_86, c_1316])).
% 5.46/2.06  tff(c_1322, plain, (v2_funct_2('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_1319])).
% 5.46/2.06  tff(c_1324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1113, c_1322])).
% 5.46/2.06  tff(c_1325, plain, (k2_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_1112])).
% 5.46/2.06  tff(c_24, plain, (![A_18]: (k10_relat_1(A_18, k2_relat_1(A_18))=k1_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.46/2.06  tff(c_1333, plain, (k10_relat_1('#skF_6', '#skF_4')=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1325, c_24])).
% 5.46/2.06  tff(c_1339, plain, (k10_relat_1('#skF_6', '#skF_4')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1036, c_1333])).
% 5.46/2.06  tff(c_1634, plain, (![A_321, D_322, B_323]: (r2_hidden(k1_funct_1(A_321, D_322), B_323) | ~r2_hidden(D_322, k10_relat_1(A_321, B_323)) | ~v1_funct_1(A_321) | ~v1_relat_1(A_321))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.46/2.06  tff(c_48, plain, (![B_36, A_35]: (~r1_tarski(B_36, A_35) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.46/2.06  tff(c_1829, plain, (![B_341, A_342, D_343]: (~r1_tarski(B_341, k1_funct_1(A_342, D_343)) | ~r2_hidden(D_343, k10_relat_1(A_342, B_341)) | ~v1_funct_1(A_342) | ~v1_relat_1(A_342))), inference(resolution, [status(thm)], [c_1634, c_48])).
% 5.46/2.06  tff(c_1846, plain, (![D_343]: (~r1_tarski('#skF_4', k1_funct_1('#skF_6', D_343)) | ~r2_hidden(D_343, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1339, c_1829])).
% 5.46/2.06  tff(c_1859, plain, (![D_343]: (~r1_tarski('#skF_4', k1_funct_1('#skF_6', D_343)) | ~r2_hidden(D_343, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_1036, c_92, c_1846])).
% 5.46/2.06  tff(c_1955, plain, (![A_359, B_360]: (~r1_tarski('#skF_4', k1_funct_1('#skF_6', '#skF_1'(A_359, B_360))) | ~r1_tarski('#skF_4', k1_relat_1('#skF_6')) | ~r1_tarski(A_359, '#skF_5') | r1_tarski(A_359, B_360))), inference(resolution, [status(thm)], [c_1929, c_1859])).
% 5.46/2.06  tff(c_2003, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_1955])).
% 5.46/2.06  tff(c_2333, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2329, c_2003])).
% 5.46/2.06  tff(c_2349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2333])).
% 5.46/2.06  tff(c_2350, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2328])).
% 5.46/2.06  tff(c_16, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.46/2.06  tff(c_1968, plain, (![B_366, A_367, B_368]: (~r1_tarski(B_366, '#skF_1'(A_367, B_368)) | ~r1_tarski('#skF_4', B_366) | ~r1_tarski(A_367, '#skF_5') | r1_tarski(A_367, B_368))), inference(resolution, [status(thm)], [c_1929, c_48])).
% 5.46/2.06  tff(c_1978, plain, (![A_367, B_368]: (~r1_tarski('#skF_4', k1_xboole_0) | ~r1_tarski(A_367, '#skF_5') | r1_tarski(A_367, B_368))), inference(resolution, [status(thm)], [c_16, c_1968])).
% 5.46/2.06  tff(c_1980, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1978])).
% 5.46/2.06  tff(c_2359, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2350, c_1980])).
% 5.46/2.06  tff(c_2371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2359])).
% 5.46/2.06  tff(c_2373, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_1955])).
% 5.46/2.06  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.46/2.06  tff(c_1960, plain, (![B_361, A_359]: (~r1_tarski('#skF_4', B_361) | ~r1_tarski(A_359, '#skF_5') | r1_tarski(A_359, B_361))), inference(resolution, [status(thm)], [c_1929, c_4])).
% 5.46/2.06  tff(c_2401, plain, (![A_359]: (~r1_tarski(A_359, '#skF_5') | r1_tarski(A_359, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_2373, c_1960])).
% 5.46/2.06  tff(c_2591, plain, (![B_407, A_408]: (k10_relat_1(B_407, k9_relat_1(B_407, A_408))=A_408 | ~v2_funct_1(B_407) | ~r1_tarski(A_408, k1_relat_1(B_407)) | ~v1_funct_1(B_407) | ~v1_relat_1(B_407))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.46/2.06  tff(c_2593, plain, (![A_359]: (k10_relat_1('#skF_6', k9_relat_1('#skF_6', A_359))=A_359 | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r1_tarski(A_359, '#skF_5'))), inference(resolution, [status(thm)], [c_2401, c_2591])).
% 5.46/2.06  tff(c_2705, plain, (![A_416]: (k10_relat_1('#skF_6', k9_relat_1('#skF_6', A_416))=A_416 | ~r1_tarski(A_416, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1036, c_92, c_1828, c_2593])).
% 5.46/2.06  tff(c_1777, plain, (![A_331, B_332, C_333, D_334]: (k8_relset_1(A_331, B_332, C_333, D_334)=k10_relat_1(C_333, D_334) | ~m1_subset_1(C_333, k1_zfmisc_1(k2_zfmisc_1(A_331, B_332))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.46/2.06  tff(c_1780, plain, (![D_334]: (k8_relset_1('#skF_4', '#skF_4', '#skF_6', D_334)=k10_relat_1('#skF_6', D_334))), inference(resolution, [status(thm)], [c_86, c_1777])).
% 5.46/2.06  tff(c_1511, plain, (![A_311, B_312, C_313, D_314]: (k7_relset_1(A_311, B_312, C_313, D_314)=k9_relat_1(C_313, D_314) | ~m1_subset_1(C_313, k1_zfmisc_1(k2_zfmisc_1(A_311, B_312))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.46/2.06  tff(c_1514, plain, (![D_314]: (k7_relset_1('#skF_4', '#skF_4', '#skF_6', D_314)=k9_relat_1('#skF_6', D_314))), inference(resolution, [status(thm)], [c_86, c_1511])).
% 5.46/2.06  tff(c_142, plain, (![B_69, A_70]: (v1_relat_1(B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.46/2.06  tff(c_145, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_86, c_142])).
% 5.46/2.06  tff(c_148, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_145])).
% 5.46/2.06  tff(c_213, plain, (![C_87, B_88, A_89]: (v5_relat_1(C_87, B_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.46/2.06  tff(c_217, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_86, c_213])).
% 5.46/2.06  tff(c_233, plain, (![B_93, A_94]: (k2_relat_1(B_93)=A_94 | ~v2_funct_2(B_93, A_94) | ~v5_relat_1(B_93, A_94) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.46/2.06  tff(c_236, plain, (k2_relat_1('#skF_6')='#skF_4' | ~v2_funct_2('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_217, c_233])).
% 5.46/2.06  tff(c_239, plain, (k2_relat_1('#skF_6')='#skF_4' | ~v2_funct_2('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_236])).
% 5.46/2.06  tff(c_240, plain, (~v2_funct_2('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_239])).
% 5.46/2.06  tff(c_492, plain, (![C_157, B_158, A_159]: (v2_funct_2(C_157, B_158) | ~v3_funct_2(C_157, A_159, B_158) | ~v1_funct_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_159, B_158))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.46/2.06  tff(c_495, plain, (v2_funct_2('#skF_6', '#skF_4') | ~v3_funct_2('#skF_6', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_86, c_492])).
% 5.46/2.06  tff(c_498, plain, (v2_funct_2('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_495])).
% 5.46/2.06  tff(c_500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_498])).
% 5.46/2.06  tff(c_501, plain, (k2_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_239])).
% 5.46/2.06  tff(c_789, plain, (![B_188, A_189]: (k9_relat_1(B_188, k10_relat_1(B_188, A_189))=A_189 | ~r1_tarski(A_189, k2_relat_1(B_188)) | ~v1_funct_1(B_188) | ~v1_relat_1(B_188))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.46/2.06  tff(c_791, plain, (![A_189]: (k9_relat_1('#skF_6', k10_relat_1('#skF_6', A_189))=A_189 | ~r1_tarski(A_189, '#skF_4') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_501, c_789])).
% 5.46/2.06  tff(c_799, plain, (![A_189]: (k9_relat_1('#skF_6', k10_relat_1('#skF_6', A_189))=A_189 | ~r1_tarski(A_189, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_92, c_791])).
% 5.46/2.06  tff(c_958, plain, (![A_208, B_209, C_210, D_211]: (k7_relset_1(A_208, B_209, C_210, D_211)=k9_relat_1(C_210, D_211) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.46/2.06  tff(c_961, plain, (![D_211]: (k7_relset_1('#skF_4', '#skF_4', '#skF_6', D_211)=k9_relat_1('#skF_6', D_211))), inference(resolution, [status(thm)], [c_86, c_958])).
% 5.46/2.06  tff(c_943, plain, (![A_201, B_202, C_203, D_204]: (k8_relset_1(A_201, B_202, C_203, D_204)=k10_relat_1(C_203, D_204) | ~m1_subset_1(C_203, k1_zfmisc_1(k2_zfmisc_1(A_201, B_202))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.46/2.06  tff(c_946, plain, (![D_204]: (k8_relset_1('#skF_4', '#skF_4', '#skF_6', D_204)=k10_relat_1('#skF_6', D_204))), inference(resolution, [status(thm)], [c_86, c_943])).
% 5.46/2.06  tff(c_82, plain, (k8_relset_1('#skF_4', '#skF_4', '#skF_6', k7_relset_1('#skF_4', '#skF_4', '#skF_6', '#skF_5'))!='#skF_5' | k7_relset_1('#skF_4', '#skF_4', '#skF_6', k8_relset_1('#skF_4', '#skF_4', '#skF_6', '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_169])).
% 5.46/2.06  tff(c_98, plain, (k7_relset_1('#skF_4', '#skF_4', '#skF_6', k8_relset_1('#skF_4', '#skF_4', '#skF_6', '#skF_5'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_82])).
% 5.46/2.06  tff(c_947, plain, (k7_relset_1('#skF_4', '#skF_4', '#skF_6', k10_relat_1('#skF_6', '#skF_5'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_946, c_98])).
% 5.46/2.06  tff(c_963, plain, (k9_relat_1('#skF_6', k10_relat_1('#skF_6', '#skF_5'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_961, c_947])).
% 5.46/2.06  tff(c_975, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_799, c_963])).
% 5.46/2.06  tff(c_979, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_975])).
% 5.46/2.06  tff(c_980, plain, (k8_relset_1('#skF_4', '#skF_4', '#skF_6', k7_relset_1('#skF_4', '#skF_4', '#skF_6', '#skF_5'))!='#skF_5'), inference(splitRight, [status(thm)], [c_82])).
% 5.46/2.06  tff(c_1541, plain, (k8_relset_1('#skF_4', '#skF_4', '#skF_6', k9_relat_1('#skF_6', '#skF_5'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1514, c_980])).
% 5.46/2.06  tff(c_1783, plain, (k10_relat_1('#skF_6', k9_relat_1('#skF_6', '#skF_5'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1780, c_1541])).
% 5.46/2.06  tff(c_2720, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2705, c_1783])).
% 5.46/2.06  tff(c_2778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2720])).
% 5.46/2.06  tff(c_2780, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1978])).
% 5.46/2.06  tff(c_1402, plain, (![B_299, A_300, B_301]: (~r1_tarski(B_299, '#skF_1'(A_300, B_301)) | ~r1_tarski(A_300, B_299) | r1_tarski(A_300, B_301))), inference(resolution, [status(thm)], [c_1388, c_48])).
% 5.46/2.06  tff(c_1412, plain, (![A_300, B_301]: (~r1_tarski(A_300, k1_xboole_0) | r1_tarski(A_300, B_301))), inference(resolution, [status(thm)], [c_16, c_1402])).
% 5.46/2.06  tff(c_2804, plain, (![B_301]: (r1_tarski('#skF_4', B_301))), inference(resolution, [status(thm)], [c_2780, c_1412])).
% 5.46/2.06  tff(c_1053, plain, (![B_226, A_227]: (B_226=A_227 | ~r1_tarski(B_226, A_227) | ~r1_tarski(A_227, B_226))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.46/2.06  tff(c_1065, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_84, c_1053])).
% 5.46/2.06  tff(c_1079, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_1065])).
% 5.46/2.06  tff(c_2843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2804, c_1079])).
% 5.46/2.06  tff(c_2844, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_1065])).
% 5.46/2.06  tff(c_2876, plain, (k8_relset_1('#skF_4', '#skF_4', '#skF_6', k7_relset_1('#skF_4', '#skF_4', '#skF_6', '#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2844, c_2844, c_980])).
% 5.46/2.06  tff(c_3543, plain, (k8_relset_1('#skF_4', '#skF_4', '#skF_6', k9_relat_1('#skF_6', '#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3524, c_2876])).
% 5.46/2.06  tff(c_3569, plain, (k10_relat_1('#skF_6', k9_relat_1('#skF_6', '#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3567, c_3543])).
% 5.46/2.06  tff(c_3201, plain, (![A_500, B_501, C_502]: (k1_relset_1(A_500, B_501, C_502)=k1_relat_1(C_502) | ~m1_subset_1(C_502, k1_zfmisc_1(k2_zfmisc_1(A_500, B_501))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.46/2.06  tff(c_3205, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_86, c_3201])).
% 5.46/2.06  tff(c_4010, plain, (![B_574, A_575, C_576]: (k1_xboole_0=B_574 | k1_relset_1(A_575, B_574, C_576)=A_575 | ~v1_funct_2(C_576, A_575, B_574) | ~m1_subset_1(C_576, k1_zfmisc_1(k2_zfmisc_1(A_575, B_574))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.46/2.06  tff(c_4013, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_4', '#skF_4', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_86, c_4010])).
% 5.46/2.06  tff(c_4016, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_3205, c_4013])).
% 5.46/2.06  tff(c_4017, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_4016])).
% 5.46/2.06  tff(c_2871, plain, (![C_428, B_429, A_430]: (v5_relat_1(C_428, B_429) | ~m1_subset_1(C_428, k1_zfmisc_1(k2_zfmisc_1(A_430, B_429))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.46/2.06  tff(c_2875, plain, (v5_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_86, c_2871])).
% 5.46/2.06  tff(c_2883, plain, (![B_432, A_433]: (k2_relat_1(B_432)=A_433 | ~v2_funct_2(B_432, A_433) | ~v5_relat_1(B_432, A_433) | ~v1_relat_1(B_432))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.46/2.06  tff(c_2886, plain, (k2_relat_1('#skF_6')='#skF_4' | ~v2_funct_2('#skF_6', '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2875, c_2883])).
% 5.46/2.06  tff(c_2889, plain, (k2_relat_1('#skF_6')='#skF_4' | ~v2_funct_2('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1036, c_2886])).
% 5.46/2.06  tff(c_2890, plain, (~v2_funct_2('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_2889])).
% 5.46/2.06  tff(c_3102, plain, (![C_485, B_486, A_487]: (v2_funct_2(C_485, B_486) | ~v3_funct_2(C_485, A_487, B_486) | ~v1_funct_1(C_485) | ~m1_subset_1(C_485, k1_zfmisc_1(k2_zfmisc_1(A_487, B_486))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.46/2.06  tff(c_3105, plain, (v2_funct_2('#skF_6', '#skF_4') | ~v3_funct_2('#skF_6', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_86, c_3102])).
% 5.46/2.06  tff(c_3108, plain, (v2_funct_2('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_3105])).
% 5.46/2.06  tff(c_3110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2890, c_3108])).
% 5.46/2.06  tff(c_3111, plain, (k2_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_2889])).
% 5.46/2.06  tff(c_3136, plain, (k10_relat_1('#skF_6', '#skF_4')=k1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3111, c_24])).
% 5.46/2.06  tff(c_3144, plain, (k10_relat_1('#skF_6', '#skF_4')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1036, c_3136])).
% 5.46/2.06  tff(c_4034, plain, (k10_relat_1('#skF_6', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4017, c_3144])).
% 5.46/2.06  tff(c_3396, plain, (![B_517, A_518]: (k9_relat_1(B_517, k10_relat_1(B_517, A_518))=A_518 | ~r1_tarski(A_518, k2_relat_1(B_517)) | ~v1_funct_1(B_517) | ~v1_relat_1(B_517))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.46/2.06  tff(c_3473, plain, (![B_522]: (k9_relat_1(B_522, k10_relat_1(B_522, k2_relat_1(B_522)))=k2_relat_1(B_522) | ~v1_funct_1(B_522) | ~v1_relat_1(B_522))), inference(resolution, [status(thm)], [c_12, c_3396])).
% 5.46/2.06  tff(c_3493, plain, (![A_18]: (k9_relat_1(A_18, k1_relat_1(A_18))=k2_relat_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18) | ~v1_relat_1(A_18))), inference(superposition, [status(thm), theory('equality')], [c_24, c_3473])).
% 5.46/2.06  tff(c_4040, plain, (k9_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4017, c_3493])).
% 5.46/2.06  tff(c_4046, plain, (k9_relat_1('#skF_6', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1036, c_1036, c_92, c_3111, c_4040])).
% 5.46/2.06  tff(c_4052, plain, (k10_relat_1('#skF_6', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4046, c_3569])).
% 5.46/2.06  tff(c_4085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4034, c_4052])).
% 5.46/2.06  tff(c_4086, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_4016])).
% 5.46/2.06  tff(c_3582, plain, (![C_537, A_538, B_539]: (v2_funct_1(C_537) | ~v3_funct_2(C_537, A_538, B_539) | ~v1_funct_1(C_537) | ~m1_subset_1(C_537, k1_zfmisc_1(k2_zfmisc_1(A_538, B_539))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.46/2.06  tff(c_3585, plain, (v2_funct_1('#skF_6') | ~v3_funct_2('#skF_6', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_86, c_3582])).
% 5.46/2.06  tff(c_3588, plain, (v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_3585])).
% 5.46/2.06  tff(c_982, plain, (![A_215, B_216]: (k3_xboole_0(A_215, B_216)=A_215 | ~r1_tarski(A_215, B_216))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.46/2.06  tff(c_993, plain, (![A_10]: (k3_xboole_0(k1_xboole_0, A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_982])).
% 5.46/2.06  tff(c_3711, plain, (![B_565, A_566]: (k10_relat_1(B_565, k9_relat_1(B_565, A_566))=A_566 | ~v2_funct_1(B_565) | ~r1_tarski(A_566, k1_relat_1(B_565)) | ~v1_funct_1(B_565) | ~v1_relat_1(B_565))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.46/2.06  tff(c_3845, plain, (![B_571]: (k10_relat_1(B_571, k9_relat_1(B_571, k1_xboole_0))=k1_xboole_0 | ~v2_funct_1(B_571) | ~v1_funct_1(B_571) | ~v1_relat_1(B_571))), inference(resolution, [status(thm)], [c_16, c_3711])).
% 5.46/2.06  tff(c_22, plain, (![B_17, A_16]: (k10_relat_1(B_17, k3_xboole_0(k2_relat_1(B_17), A_16))=k10_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.46/2.06  tff(c_3130, plain, (![A_16]: (k10_relat_1('#skF_6', k3_xboole_0('#skF_4', A_16))=k10_relat_1('#skF_6', A_16) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3111, c_22])).
% 5.46/2.06  tff(c_3140, plain, (![A_16]: (k10_relat_1('#skF_6', k3_xboole_0('#skF_4', A_16))=k10_relat_1('#skF_6', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_1036, c_3130])).
% 5.46/2.06  tff(c_3210, plain, (![D_503, A_504, B_505]: (r2_hidden(D_503, k1_relat_1(A_504)) | ~r2_hidden(D_503, k10_relat_1(A_504, B_505)) | ~v1_funct_1(A_504) | ~v1_relat_1(A_504))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.46/2.06  tff(c_3217, plain, (![D_503, A_16]: (r2_hidden(D_503, k1_relat_1('#skF_6')) | ~r2_hidden(D_503, k10_relat_1('#skF_6', A_16)) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3140, c_3210])).
% 5.46/2.06  tff(c_3237, plain, (![D_506, A_507]: (r2_hidden(D_506, k1_relat_1('#skF_6')) | ~r2_hidden(D_506, k10_relat_1('#skF_6', A_507)))), inference(demodulation, [status(thm), theory('equality')], [c_1036, c_92, c_3217])).
% 5.46/2.06  tff(c_3264, plain, (![A_508, B_509]: (r2_hidden('#skF_1'(k10_relat_1('#skF_6', A_508), B_509), k1_relat_1('#skF_6')) | r1_tarski(k10_relat_1('#skF_6', A_508), B_509))), inference(resolution, [status(thm)], [c_6, c_3237])).
% 5.46/2.06  tff(c_3297, plain, (![A_510]: (r1_tarski(k10_relat_1('#skF_6', A_510), k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_3264, c_4])).
% 5.46/2.06  tff(c_14, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.46/2.06  tff(c_3316, plain, (![A_510]: (k3_xboole_0(k10_relat_1('#skF_6', A_510), k1_relat_1('#skF_6'))=k10_relat_1('#skF_6', A_510))), inference(resolution, [status(thm)], [c_3297, c_14])).
% 5.46/2.06  tff(c_3881, plain, (k3_xboole_0(k1_xboole_0, k1_relat_1('#skF_6'))=k10_relat_1('#skF_6', k9_relat_1('#skF_6', k1_xboole_0)) | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3845, c_3316])).
% 5.46/2.06  tff(c_3918, plain, (k10_relat_1('#skF_6', k9_relat_1('#skF_6', k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1036, c_92, c_3588, c_993, c_3881])).
% 5.46/2.06  tff(c_4092, plain, (k10_relat_1('#skF_6', k9_relat_1('#skF_6', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4086, c_4086, c_3918])).
% 5.46/2.06  tff(c_4104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3569, c_4092])).
% 5.46/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.46/2.06  
% 5.46/2.06  Inference rules
% 5.46/2.06  ----------------------
% 5.46/2.06  #Ref     : 0
% 5.46/2.06  #Sup     : 870
% 5.46/2.06  #Fact    : 0
% 5.46/2.06  #Define  : 0
% 5.46/2.06  #Split   : 14
% 5.46/2.06  #Chain   : 0
% 5.46/2.06  #Close   : 0
% 5.46/2.06  
% 5.46/2.06  Ordering : KBO
% 5.46/2.06  
% 5.46/2.06  Simplification rules
% 5.46/2.06  ----------------------
% 5.46/2.06  #Subsume      : 140
% 5.46/2.06  #Demod        : 871
% 5.46/2.06  #Tautology    : 401
% 5.46/2.06  #SimpNegUnit  : 4
% 5.46/2.06  #BackRed      : 105
% 5.46/2.06  
% 5.46/2.06  #Partial instantiations: 0
% 5.46/2.06  #Strategies tried      : 1
% 5.46/2.06  
% 5.46/2.06  Timing (in seconds)
% 5.46/2.06  ----------------------
% 5.46/2.07  Preprocessing        : 0.38
% 5.46/2.07  Parsing              : 0.20
% 5.46/2.07  CNF conversion       : 0.03
% 5.46/2.07  Main loop            : 0.81
% 5.46/2.07  Inferencing          : 0.30
% 5.46/2.07  Reduction            : 0.26
% 5.46/2.07  Demodulation         : 0.19
% 5.46/2.07  BG Simplification    : 0.04
% 5.46/2.07  Subsumption          : 0.14
% 5.46/2.07  Abstraction          : 0.04
% 5.46/2.07  MUC search           : 0.00
% 5.46/2.07  Cooper               : 0.00
% 5.46/2.07  Total                : 1.25
% 5.46/2.07  Index Insertion      : 0.00
% 5.46/2.07  Index Deletion       : 0.00
% 5.46/2.07  Index Matching       : 0.00
% 5.46/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
