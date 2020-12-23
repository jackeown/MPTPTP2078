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
% DateTime   : Thu Dec  3 10:10:50 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 167 expanded)
%              Number of leaves         :   26 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :  115 ( 389 expanded)
%              Number of equality atoms :   49 ( 137 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_79,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_66,axiom,(
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

tff(f_36,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2685,plain,(
    ! [A_2299] :
      ( r1_tarski(A_2299,k2_zfmisc_1(k1_relat_1(A_2299),k2_relat_1(A_2299)))
      | ~ v1_relat_1(A_2299) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [A_11,B_12] : v1_funct_2('#skF_1'(A_11,B_12),A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_40,plain,(
    ! [A_11,B_12] : m1_subset_1('#skF_1'(A_11,B_12),k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2399,plain,(
    ! [A_2263,B_2264,C_2265] :
      ( k1_relset_1(A_2263,B_2264,C_2265) = k1_relat_1(C_2265)
      | ~ m1_subset_1(C_2265,k1_zfmisc_1(k2_zfmisc_1(A_2263,B_2264))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2407,plain,(
    ! [A_11,B_12] : k1_relset_1(A_11,B_12,'#skF_1'(A_11,B_12)) = k1_relat_1('#skF_1'(A_11,B_12)) ),
    inference(resolution,[status(thm)],[c_40,c_2399])).

tff(c_6,plain,(
    ! [A_3] :
      ( r1_tarski(A_3,k2_zfmisc_1(k1_relat_1(A_3),k2_relat_1(A_3)))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_308,plain,(
    ! [A_308,B_309,C_310] :
      ( k1_relset_1(A_308,B_309,C_310) = k1_relat_1(C_310)
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(A_308,B_309))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_331,plain,(
    ! [A_317,B_318,A_319] :
      ( k1_relset_1(A_317,B_318,A_319) = k1_relat_1(A_319)
      | ~ r1_tarski(A_319,k2_zfmisc_1(A_317,B_318)) ) ),
    inference(resolution,[status(thm)],[c_4,c_308])).

tff(c_343,plain,(
    ! [A_3] :
      ( k1_relset_1(k1_relat_1(A_3),k2_relat_1(A_3),A_3) = k1_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_331])).

tff(c_63,plain,(
    ! [A_24] :
      ( k2_relat_1(A_24) != k1_xboole_0
      | k1_xboole_0 = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_71,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_46,c_63])).

tff(c_72,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_571,plain,(
    ! [B_337,C_338,A_339] :
      ( k1_xboole_0 = B_337
      | v1_funct_2(C_338,A_339,B_337)
      | k1_relset_1(A_339,B_337,C_338) != A_339
      | ~ m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(A_339,B_337))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2101,plain,(
    ! [B_2245,A_2246,A_2247] :
      ( k1_xboole_0 = B_2245
      | v1_funct_2(A_2246,A_2247,B_2245)
      | k1_relset_1(A_2247,B_2245,A_2246) != A_2247
      | ~ r1_tarski(A_2246,k2_zfmisc_1(A_2247,B_2245)) ) ),
    inference(resolution,[status(thm)],[c_4,c_571])).

tff(c_2289,plain,(
    ! [A_2251] :
      ( k2_relat_1(A_2251) = k1_xboole_0
      | v1_funct_2(A_2251,k1_relat_1(A_2251),k2_relat_1(A_2251))
      | k1_relset_1(k1_relat_1(A_2251),k2_relat_1(A_2251),A_2251) != k1_relat_1(A_2251)
      | ~ v1_relat_1(A_2251) ) ),
    inference(resolution,[status(thm)],[c_6,c_2101])).

tff(c_44,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42])).

tff(c_62,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_2292,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2289,c_62])).

tff(c_2310,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2292])).

tff(c_2311,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2310])).

tff(c_2324,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_2311])).

tff(c_2328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2324])).

tff(c_2329,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_26,plain,(
    ! [B_9,C_10] :
      ( k1_relset_1(k1_xboole_0,B_9,C_10) = k1_xboole_0
      | ~ v1_funct_2(C_10,k1_xboole_0,B_9)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2534,plain,(
    ! [B_2282,C_2283] :
      ( k1_relset_1('#skF_2',B_2282,C_2283) = '#skF_2'
      | ~ v1_funct_2(C_2283,'#skF_2',B_2282)
      | ~ m1_subset_1(C_2283,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_2282))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2329,c_2329,c_2329,c_2329,c_26])).

tff(c_2538,plain,(
    ! [B_12] :
      ( k1_relset_1('#skF_2',B_12,'#skF_1'('#skF_2',B_12)) = '#skF_2'
      | ~ v1_funct_2('#skF_1'('#skF_2',B_12),'#skF_2',B_12) ) ),
    inference(resolution,[status(thm)],[c_40,c_2534])).

tff(c_2547,plain,(
    ! [B_2284] : k1_relat_1('#skF_1'('#skF_2',B_2284)) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2407,c_2538])).

tff(c_38,plain,(
    ! [A_11,B_12] : v1_relat_1('#skF_1'(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14,plain,(
    ! [A_4] :
      ( k1_relat_1(A_4) != k1_xboole_0
      | k1_xboole_0 = A_4
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2357,plain,(
    ! [A_2256] :
      ( k1_relat_1(A_2256) != '#skF_2'
      | A_2256 = '#skF_2'
      | ~ v1_relat_1(A_2256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2329,c_2329,c_14])).

tff(c_2364,plain,(
    ! [A_11,B_12] :
      ( k1_relat_1('#skF_1'(A_11,B_12)) != '#skF_2'
      | '#skF_1'(A_11,B_12) = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_38,c_2357])).

tff(c_2576,plain,(
    ! [B_2285] : '#skF_1'('#skF_2',B_2285) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2547,c_2364])).

tff(c_2600,plain,(
    ! [B_2285] : v1_funct_2('#skF_2','#skF_2',B_2285) ),
    inference(superposition,[status(thm),theory(equality)],[c_2576,c_30])).

tff(c_10,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2333,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2329,c_2329,c_10])).

tff(c_2330,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_2338,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2329,c_2330])).

tff(c_2339,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2338,c_62])).

tff(c_2350,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2333,c_2339])).

tff(c_2646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2600,c_2350])).

tff(c_2647,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2684,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_4,c_2647])).

tff(c_2688,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2685,c_2684])).

tff(c_2698,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2688])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 17:59:38 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.61  
% 3.75/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.61  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.75/1.61  
% 3.75/1.61  %Foreground sorts:
% 3.75/1.61  
% 3.75/1.61  
% 3.75/1.61  %Background operators:
% 3.75/1.61  
% 3.75/1.61  
% 3.75/1.61  %Foreground operators:
% 3.75/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.75/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.75/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.75/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.75/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.75/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.75/1.61  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.75/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.75/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.75/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.75/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.75/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.75/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.75/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.75/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.75/1.61  
% 3.75/1.62  tff(f_90, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 3.75/1.62  tff(f_33, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.75/1.62  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.75/1.62  tff(f_79, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 3.75/1.62  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.75/1.62  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.75/1.62  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.75/1.62  tff(f_36, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.75/1.62  tff(c_46, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.75/1.62  tff(c_2685, plain, (![A_2299]: (r1_tarski(A_2299, k2_zfmisc_1(k1_relat_1(A_2299), k2_relat_1(A_2299))) | ~v1_relat_1(A_2299))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.75/1.62  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.75/1.62  tff(c_30, plain, (![A_11, B_12]: (v1_funct_2('#skF_1'(A_11, B_12), A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.75/1.62  tff(c_40, plain, (![A_11, B_12]: (m1_subset_1('#skF_1'(A_11, B_12), k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.75/1.62  tff(c_2399, plain, (![A_2263, B_2264, C_2265]: (k1_relset_1(A_2263, B_2264, C_2265)=k1_relat_1(C_2265) | ~m1_subset_1(C_2265, k1_zfmisc_1(k2_zfmisc_1(A_2263, B_2264))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.75/1.62  tff(c_2407, plain, (![A_11, B_12]: (k1_relset_1(A_11, B_12, '#skF_1'(A_11, B_12))=k1_relat_1('#skF_1'(A_11, B_12)))), inference(resolution, [status(thm)], [c_40, c_2399])).
% 3.75/1.62  tff(c_6, plain, (![A_3]: (r1_tarski(A_3, k2_zfmisc_1(k1_relat_1(A_3), k2_relat_1(A_3))) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.75/1.62  tff(c_308, plain, (![A_308, B_309, C_310]: (k1_relset_1(A_308, B_309, C_310)=k1_relat_1(C_310) | ~m1_subset_1(C_310, k1_zfmisc_1(k2_zfmisc_1(A_308, B_309))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.75/1.62  tff(c_331, plain, (![A_317, B_318, A_319]: (k1_relset_1(A_317, B_318, A_319)=k1_relat_1(A_319) | ~r1_tarski(A_319, k2_zfmisc_1(A_317, B_318)))), inference(resolution, [status(thm)], [c_4, c_308])).
% 3.75/1.62  tff(c_343, plain, (![A_3]: (k1_relset_1(k1_relat_1(A_3), k2_relat_1(A_3), A_3)=k1_relat_1(A_3) | ~v1_relat_1(A_3))), inference(resolution, [status(thm)], [c_6, c_331])).
% 3.75/1.62  tff(c_63, plain, (![A_24]: (k2_relat_1(A_24)!=k1_xboole_0 | k1_xboole_0=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.75/1.62  tff(c_71, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_46, c_63])).
% 3.75/1.62  tff(c_72, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_71])).
% 3.75/1.62  tff(c_571, plain, (![B_337, C_338, A_339]: (k1_xboole_0=B_337 | v1_funct_2(C_338, A_339, B_337) | k1_relset_1(A_339, B_337, C_338)!=A_339 | ~m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(A_339, B_337))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.75/1.62  tff(c_2101, plain, (![B_2245, A_2246, A_2247]: (k1_xboole_0=B_2245 | v1_funct_2(A_2246, A_2247, B_2245) | k1_relset_1(A_2247, B_2245, A_2246)!=A_2247 | ~r1_tarski(A_2246, k2_zfmisc_1(A_2247, B_2245)))), inference(resolution, [status(thm)], [c_4, c_571])).
% 3.75/1.62  tff(c_2289, plain, (![A_2251]: (k2_relat_1(A_2251)=k1_xboole_0 | v1_funct_2(A_2251, k1_relat_1(A_2251), k2_relat_1(A_2251)) | k1_relset_1(k1_relat_1(A_2251), k2_relat_1(A_2251), A_2251)!=k1_relat_1(A_2251) | ~v1_relat_1(A_2251))), inference(resolution, [status(thm)], [c_6, c_2101])).
% 3.75/1.62  tff(c_44, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.75/1.62  tff(c_42, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.75/1.62  tff(c_48, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42])).
% 3.75/1.62  tff(c_62, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_48])).
% 3.75/1.62  tff(c_2292, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2289, c_62])).
% 3.75/1.62  tff(c_2310, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2292])).
% 3.75/1.62  tff(c_2311, plain, (k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_72, c_2310])).
% 3.75/1.62  tff(c_2324, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_343, c_2311])).
% 3.75/1.62  tff(c_2328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_2324])).
% 3.75/1.62  tff(c_2329, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_71])).
% 3.75/1.62  tff(c_26, plain, (![B_9, C_10]: (k1_relset_1(k1_xboole_0, B_9, C_10)=k1_xboole_0 | ~v1_funct_2(C_10, k1_xboole_0, B_9) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_9))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.75/1.62  tff(c_2534, plain, (![B_2282, C_2283]: (k1_relset_1('#skF_2', B_2282, C_2283)='#skF_2' | ~v1_funct_2(C_2283, '#skF_2', B_2282) | ~m1_subset_1(C_2283, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_2282))))), inference(demodulation, [status(thm), theory('equality')], [c_2329, c_2329, c_2329, c_2329, c_26])).
% 3.75/1.62  tff(c_2538, plain, (![B_12]: (k1_relset_1('#skF_2', B_12, '#skF_1'('#skF_2', B_12))='#skF_2' | ~v1_funct_2('#skF_1'('#skF_2', B_12), '#skF_2', B_12))), inference(resolution, [status(thm)], [c_40, c_2534])).
% 3.75/1.62  tff(c_2547, plain, (![B_2284]: (k1_relat_1('#skF_1'('#skF_2', B_2284))='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2407, c_2538])).
% 3.75/1.62  tff(c_38, plain, (![A_11, B_12]: (v1_relat_1('#skF_1'(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.75/1.62  tff(c_14, plain, (![A_4]: (k1_relat_1(A_4)!=k1_xboole_0 | k1_xboole_0=A_4 | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.75/1.62  tff(c_2357, plain, (![A_2256]: (k1_relat_1(A_2256)!='#skF_2' | A_2256='#skF_2' | ~v1_relat_1(A_2256))), inference(demodulation, [status(thm), theory('equality')], [c_2329, c_2329, c_14])).
% 3.75/1.62  tff(c_2364, plain, (![A_11, B_12]: (k1_relat_1('#skF_1'(A_11, B_12))!='#skF_2' | '#skF_1'(A_11, B_12)='#skF_2')), inference(resolution, [status(thm)], [c_38, c_2357])).
% 3.75/1.62  tff(c_2576, plain, (![B_2285]: ('#skF_1'('#skF_2', B_2285)='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2547, c_2364])).
% 3.75/1.62  tff(c_2600, plain, (![B_2285]: (v1_funct_2('#skF_2', '#skF_2', B_2285))), inference(superposition, [status(thm), theory('equality')], [c_2576, c_30])).
% 3.75/1.62  tff(c_10, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.75/1.62  tff(c_2333, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2329, c_2329, c_10])).
% 3.75/1.62  tff(c_2330, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_71])).
% 3.75/1.62  tff(c_2338, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2329, c_2330])).
% 3.75/1.62  tff(c_2339, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2338, c_62])).
% 3.75/1.62  tff(c_2350, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2333, c_2339])).
% 3.75/1.62  tff(c_2646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2600, c_2350])).
% 3.75/1.62  tff(c_2647, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_48])).
% 3.75/1.62  tff(c_2684, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_4, c_2647])).
% 3.75/1.62  tff(c_2688, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2685, c_2684])).
% 3.75/1.62  tff(c_2698, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_2688])).
% 3.75/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.62  
% 3.75/1.62  Inference rules
% 3.75/1.62  ----------------------
% 3.75/1.62  #Ref     : 0
% 3.75/1.62  #Sup     : 532
% 3.75/1.62  #Fact    : 4
% 3.75/1.62  #Define  : 0
% 3.75/1.62  #Split   : 11
% 3.75/1.62  #Chain   : 0
% 3.75/1.62  #Close   : 0
% 3.75/1.62  
% 3.75/1.62  Ordering : KBO
% 3.75/1.62  
% 3.75/1.62  Simplification rules
% 3.75/1.62  ----------------------
% 3.75/1.62  #Subsume      : 121
% 3.75/1.62  #Demod        : 337
% 3.75/1.62  #Tautology    : 241
% 3.75/1.62  #SimpNegUnit  : 3
% 3.75/1.62  #BackRed      : 7
% 3.75/1.62  
% 3.75/1.62  #Partial instantiations: 207
% 3.75/1.62  #Strategies tried      : 1
% 3.75/1.62  
% 3.75/1.62  Timing (in seconds)
% 3.75/1.62  ----------------------
% 3.75/1.63  Preprocessing        : 0.30
% 3.75/1.63  Parsing              : 0.15
% 3.75/1.63  CNF conversion       : 0.02
% 3.75/1.63  Main loop            : 0.56
% 3.75/1.63  Inferencing          : 0.24
% 3.75/1.63  Reduction            : 0.16
% 3.75/1.63  Demodulation         : 0.12
% 3.75/1.63  BG Simplification    : 0.03
% 3.75/1.63  Subsumption          : 0.09
% 3.75/1.63  Abstraction          : 0.03
% 3.75/1.63  MUC search           : 0.00
% 3.75/1.63  Cooper               : 0.00
% 3.75/1.63  Total                : 0.89
% 3.75/1.63  Index Insertion      : 0.00
% 3.75/1.63  Index Deletion       : 0.00
% 3.75/1.63  Index Matching       : 0.00
% 3.75/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
