%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:38 EST 2020

% Result     : Theorem 13.95s
% Output     : CNFRefutation 13.95s
% Verified   : 
% Statistics : Number of formulae       :  190 (1083 expanded)
%              Number of leaves         :   47 ( 334 expanded)
%              Depth                    :   15
%              Number of atoms          :  302 (3076 expanded)
%              Number of equality atoms :  100 ( 581 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_172,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ~ v1_xboole_0(D)
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,A,D)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,D))) )
           => ( ( r1_tarski(B,A)
                & r1_tarski(k7_relset_1(A,D,E,B),C) )
             => ( v1_funct_1(k2_partfun1(A,D,E,B))
                & v1_funct_2(k2_partfun1(A,D,E,B),B,C)
                & m1_subset_1(k2_partfun1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_77,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_127,axiom,(
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

tff(f_87,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_141,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_135,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_90,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_82,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_38,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_84,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_144,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_153,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(resolution,[status(thm)],[c_84,c_144])).

tff(c_159,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_153])).

tff(c_86,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_31258,plain,(
    ! [A_2075,B_2076,C_2077] :
      ( k1_relset_1(A_2075,B_2076,C_2077) = k1_relat_1(C_2077)
      | ~ m1_subset_1(C_2077,k1_zfmisc_1(k2_zfmisc_1(A_2075,B_2076))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_31287,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_31258])).

tff(c_32559,plain,(
    ! [B_2186,A_2187,C_2188] :
      ( k1_xboole_0 = B_2186
      | k1_relset_1(A_2187,B_2186,C_2188) = A_2187
      | ~ v1_funct_2(C_2188,A_2187,B_2186)
      | ~ m1_subset_1(C_2188,k1_zfmisc_1(k2_zfmisc_1(A_2187,B_2186))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_32579,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_32559])).

tff(c_32590,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_31287,c_32579])).

tff(c_32592,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_32590])).

tff(c_42,plain,(
    ! [B_25,A_24] :
      ( k1_relat_1(k7_relat_1(B_25,A_24)) = A_24
      | ~ r1_tarski(A_24,k1_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32630,plain,(
    ! [A_24] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_24)) = A_24
      | ~ r1_tarski(A_24,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32592,c_42])).

tff(c_32669,plain,(
    ! [A_24] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_24)) = A_24
      | ~ r1_tarski(A_24,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_32630])).

tff(c_88,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_32455,plain,(
    ! [A_2179,B_2180,C_2181,D_2182] :
      ( k2_partfun1(A_2179,B_2180,C_2181,D_2182) = k7_relat_1(C_2181,D_2182)
      | ~ m1_subset_1(C_2181,k1_zfmisc_1(k2_zfmisc_1(A_2179,B_2180)))
      | ~ v1_funct_1(C_2181) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_32471,plain,(
    ! [D_2182] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_2182) = k7_relat_1('#skF_5',D_2182)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_84,c_32455])).

tff(c_32485,plain,(
    ! [D_2182] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_2182) = k7_relat_1('#skF_5',D_2182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_32471])).

tff(c_8114,plain,(
    ! [A_622,B_623,C_624,D_625] :
      ( k7_relset_1(A_622,B_623,C_624,D_625) = k9_relat_1(C_624,D_625)
      | ~ m1_subset_1(C_624,k1_zfmisc_1(k2_zfmisc_1(A_622,B_623))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_8132,plain,(
    ! [D_625] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_625) = k9_relat_1('#skF_5',D_625) ),
    inference(resolution,[status(thm)],[c_84,c_8114])).

tff(c_80,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_8228,plain,(
    r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8132,c_80])).

tff(c_40,plain,(
    ! [B_23,A_22] :
      ( k2_relat_1(k7_relat_1(B_23,A_22)) = k9_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2831,plain,(
    ! [C_242,A_243,B_244] :
      ( v4_relat_1(C_242,A_243)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2851,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_2831])).

tff(c_2931,plain,(
    ! [C_261,A_262,B_263] :
      ( v1_relat_1(k7_relat_1(C_261,A_262))
      | ~ v4_relat_1(C_261,B_263)
      | ~ v1_relat_1(C_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2939,plain,(
    ! [A_262] :
      ( v1_relat_1(k7_relat_1('#skF_5',A_262))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2851,c_2931])).

tff(c_2949,plain,(
    ! [A_262] : v1_relat_1(k7_relat_1('#skF_5',A_262)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_2939])).

tff(c_3149,plain,(
    ! [C_302,A_303,B_304] :
      ( v4_relat_1(k7_relat_1(C_302,A_303),A_303)
      | ~ v4_relat_1(C_302,B_304)
      | ~ v1_relat_1(C_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3159,plain,(
    ! [A_303] :
      ( v4_relat_1(k7_relat_1('#skF_5',A_303),A_303)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2851,c_3149])).

tff(c_3170,plain,(
    ! [A_303] : v4_relat_1(k7_relat_1('#skF_5',A_303),A_303) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_3159])).

tff(c_30,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8316,plain,(
    ! [C_640,A_641,B_642] :
      ( m1_subset_1(C_640,k1_zfmisc_1(k2_zfmisc_1(A_641,B_642)))
      | ~ r1_tarski(k2_relat_1(C_640),B_642)
      | ~ r1_tarski(k1_relat_1(C_640),A_641)
      | ~ v1_relat_1(C_640) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_8251,plain,(
    ! [A_628,B_629,C_630,D_631] :
      ( k2_partfun1(A_628,B_629,C_630,D_631) = k7_relat_1(C_630,D_631)
      | ~ m1_subset_1(C_630,k1_zfmisc_1(k2_zfmisc_1(A_628,B_629)))
      | ~ v1_funct_1(C_630) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_8263,plain,(
    ! [D_631] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_631) = k7_relat_1('#skF_5',D_631)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_84,c_8251])).

tff(c_8273,plain,(
    ! [D_631] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_631) = k7_relat_1('#skF_5',D_631) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_8263])).

tff(c_2749,plain,(
    ! [A_232,B_233,C_234,D_235] :
      ( v1_funct_1(k2_partfun1(A_232,B_233,C_234,D_235))
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233)))
      | ~ v1_funct_1(C_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2761,plain,(
    ! [D_235] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_235))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_84,c_2749])).

tff(c_2769,plain,(
    ! [D_235] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_235)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2761])).

tff(c_78,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_160,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_2772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2769,c_160])).

tff(c_2773,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_2775,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2773])).

tff(c_8279,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8273,c_2775])).

tff(c_8319,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_8316,c_8279])).

tff(c_8351,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2949,c_8319])).

tff(c_8368,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_8351])).

tff(c_8371,plain,
    ( ~ v4_relat_1(k7_relat_1('#skF_5','#skF_2'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_8368])).

tff(c_8375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2949,c_3170,c_8371])).

tff(c_8376,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_8351])).

tff(c_8393,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_8376])).

tff(c_8396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_8228,c_8393])).

tff(c_8398,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2773])).

tff(c_31283,plain,(
    k1_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) = k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_8398,c_31258])).

tff(c_32490,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = k1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32485,c_32485,c_31283])).

tff(c_8397,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_2773])).

tff(c_32502,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32485,c_8397])).

tff(c_32501,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32485,c_8398])).

tff(c_60,plain,(
    ! [B_40,C_41,A_39] :
      ( k1_xboole_0 = B_40
      | v1_funct_2(C_41,A_39,B_40)
      | k1_relset_1(A_39,B_40,C_41) != A_39
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_32876,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_32501,c_60])).

tff(c_32905,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_32502,c_32876])).

tff(c_33462,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32490,c_32905])).

tff(c_33463,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_33462])).

tff(c_33466,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32669,c_33463])).

tff(c_33470,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_33466])).

tff(c_33471,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_33462])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_33538,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33471,c_10])).

tff(c_14,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_33537,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33471,c_33471,c_14])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26757,plain,(
    r1_tarski(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8398,c_20])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26805,plain,
    ( k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2') = k2_zfmisc_1('#skF_2','#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26757,c_4])).

tff(c_26937,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_26805])).

tff(c_32496,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32485,c_26937])).

tff(c_33666,plain,(
    ~ r1_tarski('#skF_3',k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33537,c_32496])).

tff(c_33670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33538,c_33666])).

tff(c_33671,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32590])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_33732,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33671,c_2])).

tff(c_33734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_33732])).

tff(c_33735,plain,(
    k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2') = k2_zfmisc_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26805])).

tff(c_35886,plain,(
    ~ v1_funct_2(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33735,c_8397])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_39380,plain,(
    ! [A_2655,B_2656,C_2657] :
      ( k1_relset_1(A_2655,B_2656,C_2657) = k1_relat_1(C_2657)
      | ~ m1_subset_1(C_2657,k1_zfmisc_1(k2_zfmisc_1(A_2655,B_2656))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_39595,plain,(
    ! [A_2671,B_2672,A_2673] :
      ( k1_relset_1(A_2671,B_2672,A_2673) = k1_relat_1(A_2673)
      | ~ r1_tarski(A_2673,k2_zfmisc_1(A_2671,B_2672)) ) ),
    inference(resolution,[status(thm)],[c_22,c_39380])).

tff(c_39622,plain,(
    ! [A_2671,B_2672] : k1_relset_1(A_2671,B_2672,k2_zfmisc_1(A_2671,B_2672)) = k1_relat_1(k2_zfmisc_1(A_2671,B_2672)) ),
    inference(resolution,[status(thm)],[c_8,c_39595])).

tff(c_35885,plain,(
    m1_subset_1(k2_zfmisc_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33735,c_8398])).

tff(c_40669,plain,(
    ! [B_2752,C_2753,A_2754] :
      ( k1_xboole_0 = B_2752
      | v1_funct_2(C_2753,A_2754,B_2752)
      | k1_relset_1(A_2754,B_2752,C_2753) != A_2754
      | ~ m1_subset_1(C_2753,k1_zfmisc_1(k2_zfmisc_1(A_2754,B_2752))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_40678,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k2_zfmisc_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_35885,c_40669])).

tff(c_40699,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_2','#skF_3')
    | k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39622,c_40678])).

tff(c_40700,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_35886,c_40699])).

tff(c_40812,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_40700])).

tff(c_40162,plain,(
    ! [A_2730,B_2731,C_2732,D_2733] :
      ( k2_partfun1(A_2730,B_2731,C_2732,D_2733) = k7_relat_1(C_2732,D_2733)
      | ~ m1_subset_1(C_2732,k1_zfmisc_1(k2_zfmisc_1(A_2730,B_2731)))
      | ~ v1_funct_1(C_2732) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_40176,plain,(
    ! [D_2733] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_2733) = k7_relat_1('#skF_5',D_2733)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_84,c_40162])).

tff(c_40191,plain,(
    ! [D_2734] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_2734) = k7_relat_1('#skF_5',D_2734) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_40176])).

tff(c_40197,plain,(
    k7_relat_1('#skF_5','#skF_2') = k2_zfmisc_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_40191,c_33735])).

tff(c_39409,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_84,c_39380])).

tff(c_40441,plain,(
    ! [B_2747,A_2748,C_2749] :
      ( k1_xboole_0 = B_2747
      | k1_relset_1(A_2748,B_2747,C_2749) = A_2748
      | ~ v1_funct_2(C_2749,A_2748,B_2747)
      | ~ m1_subset_1(C_2749,k1_zfmisc_1(k2_zfmisc_1(A_2748,B_2747))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_40464,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_40441])).

tff(c_40477,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_39409,c_40464])).

tff(c_40479,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_40477])).

tff(c_40512,plain,(
    ! [A_24] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_24)) = A_24
      | ~ r1_tarski(A_24,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40479,c_42])).

tff(c_41104,plain,(
    ! [A_2770] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_2770)) = A_2770
      | ~ r1_tarski(A_2770,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_40512])).

tff(c_41172,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_40197,c_41104])).

tff(c_41226,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_41172])).

tff(c_41228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40812,c_41226])).

tff(c_41229,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_40700])).

tff(c_100,plain,(
    ! [A_56] : k2_zfmisc_1(A_56,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_104,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_38])).

tff(c_18,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_26696,plain,(
    ! [C_1752,A_1753,B_1754] :
      ( v4_relat_1(C_1752,A_1753)
      | ~ m1_subset_1(C_1752,k1_zfmisc_1(k2_zfmisc_1(A_1753,B_1754))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26717,plain,(
    ! [A_1755] : v4_relat_1(k1_xboole_0,A_1755) ),
    inference(resolution,[status(thm)],[c_18,c_26696])).

tff(c_26678,plain,(
    ! [B_1749,A_1750] :
      ( r1_tarski(k1_relat_1(B_1749),A_1750)
      | ~ v4_relat_1(B_1749,A_1750)
      | ~ v1_relat_1(B_1749) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8435,plain,(
    ! [B_648,A_649] :
      ( B_648 = A_649
      | ~ r1_tarski(B_648,A_649)
      | ~ r1_tarski(A_649,B_648) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8448,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_8435])).

tff(c_26692,plain,(
    ! [B_1749] :
      ( k1_relat_1(B_1749) = k1_xboole_0
      | ~ v4_relat_1(B_1749,k1_xboole_0)
      | ~ v1_relat_1(B_1749) ) ),
    inference(resolution,[status(thm)],[c_26678,c_8448])).

tff(c_26721,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26717,c_26692])).

tff(c_26724,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_26721])).

tff(c_39394,plain,(
    ! [A_2655,B_2656] : k1_relset_1(A_2655,B_2656,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_39380])).

tff(c_39408,plain,(
    ! [A_2655,B_2656] : k1_relset_1(A_2655,B_2656,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26724,c_39394])).

tff(c_16,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_58,plain,(
    ! [C_41,B_40] :
      ( v1_funct_2(C_41,k1_xboole_0,B_40)
      | k1_relset_1(k1_xboole_0,B_40,C_41) != k1_xboole_0
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_39522,plain,(
    ! [C_2660,B_2661] :
      ( v1_funct_2(C_2660,k1_xboole_0,B_2661)
      | k1_relset_1(k1_xboole_0,B_2661,C_2660) != k1_xboole_0
      | ~ m1_subset_1(C_2660,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_58])).

tff(c_39528,plain,(
    ! [B_2661] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_2661)
      | k1_relset_1(k1_xboole_0,B_2661,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_39522])).

tff(c_39532,plain,(
    ! [B_2661] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_2661) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39408,c_39528])).

tff(c_41253,plain,(
    ! [B_2661] : v1_funct_2('#skF_3','#skF_3',B_2661) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41229,c_41229,c_39532])).

tff(c_41273,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41229,c_41229,c_26724])).

tff(c_41282,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41229,c_41229,c_14])).

tff(c_41230,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_40700])).

tff(c_42030,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41273,c_41282,c_41230])).

tff(c_41686,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41282,c_35886])).

tff(c_42032,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42030,c_41686])).

tff(c_42040,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41253,c_42032])).

tff(c_42041,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_40477])).

tff(c_42093,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42041,c_2])).

tff(c_42095,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_42093])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.95/5.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.95/5.84  
% 13.95/5.84  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.95/5.85  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.95/5.85  
% 13.95/5.85  %Foreground sorts:
% 13.95/5.85  
% 13.95/5.85  
% 13.95/5.85  %Background operators:
% 13.95/5.85  
% 13.95/5.85  
% 13.95/5.85  %Foreground operators:
% 13.95/5.85  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.95/5.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.95/5.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.95/5.85  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 13.95/5.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.95/5.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.95/5.85  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.95/5.85  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 13.95/5.85  tff('#skF_5', type, '#skF_5': $i).
% 13.95/5.85  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.95/5.85  tff('#skF_2', type, '#skF_2': $i).
% 13.95/5.85  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.95/5.85  tff('#skF_3', type, '#skF_3': $i).
% 13.95/5.85  tff('#skF_1', type, '#skF_1': $i).
% 13.95/5.85  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 13.95/5.85  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.95/5.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.95/5.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.95/5.85  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.95/5.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.95/5.85  tff('#skF_4', type, '#skF_4': $i).
% 13.95/5.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.95/5.85  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 13.95/5.85  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.95/5.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.95/5.85  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.95/5.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.95/5.85  
% 13.95/5.87  tff(f_172, negated_conjecture, ~(![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_funct_2)).
% 13.95/5.87  tff(f_77, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 13.95/5.87  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 13.95/5.87  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.95/5.87  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 13.95/5.87  tff(f_87, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 13.95/5.87  tff(f_141, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 13.95/5.87  tff(f_101, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 13.95/5.87  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 13.95/5.87  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.95/5.87  tff(f_75, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc23_relat_1)).
% 13.95/5.87  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 13.95/5.87  tff(f_109, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 13.95/5.87  tff(f_135, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 13.95/5.87  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.95/5.87  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 13.95/5.87  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 13.95/5.87  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.95/5.87  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 13.95/5.87  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 13.95/5.87  tff(c_90, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.95/5.87  tff(c_82, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.95/5.87  tff(c_38, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.95/5.87  tff(c_84, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.95/5.87  tff(c_144, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.95/5.87  tff(c_153, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_4'))), inference(resolution, [status(thm)], [c_84, c_144])).
% 13.95/5.87  tff(c_159, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_153])).
% 13.95/5.87  tff(c_86, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.95/5.87  tff(c_31258, plain, (![A_2075, B_2076, C_2077]: (k1_relset_1(A_2075, B_2076, C_2077)=k1_relat_1(C_2077) | ~m1_subset_1(C_2077, k1_zfmisc_1(k2_zfmisc_1(A_2075, B_2076))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 13.95/5.87  tff(c_31287, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_31258])).
% 13.95/5.87  tff(c_32559, plain, (![B_2186, A_2187, C_2188]: (k1_xboole_0=B_2186 | k1_relset_1(A_2187, B_2186, C_2188)=A_2187 | ~v1_funct_2(C_2188, A_2187, B_2186) | ~m1_subset_1(C_2188, k1_zfmisc_1(k2_zfmisc_1(A_2187, B_2186))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.95/5.87  tff(c_32579, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_84, c_32559])).
% 13.95/5.87  tff(c_32590, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_31287, c_32579])).
% 13.95/5.87  tff(c_32592, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_32590])).
% 13.95/5.87  tff(c_42, plain, (![B_25, A_24]: (k1_relat_1(k7_relat_1(B_25, A_24))=A_24 | ~r1_tarski(A_24, k1_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_87])).
% 13.95/5.87  tff(c_32630, plain, (![A_24]: (k1_relat_1(k7_relat_1('#skF_5', A_24))=A_24 | ~r1_tarski(A_24, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_32592, c_42])).
% 13.95/5.87  tff(c_32669, plain, (![A_24]: (k1_relat_1(k7_relat_1('#skF_5', A_24))=A_24 | ~r1_tarski(A_24, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_32630])).
% 13.95/5.87  tff(c_88, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.95/5.87  tff(c_32455, plain, (![A_2179, B_2180, C_2181, D_2182]: (k2_partfun1(A_2179, B_2180, C_2181, D_2182)=k7_relat_1(C_2181, D_2182) | ~m1_subset_1(C_2181, k1_zfmisc_1(k2_zfmisc_1(A_2179, B_2180))) | ~v1_funct_1(C_2181))), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.95/5.87  tff(c_32471, plain, (![D_2182]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_2182)=k7_relat_1('#skF_5', D_2182) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_84, c_32455])).
% 13.95/5.87  tff(c_32485, plain, (![D_2182]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_2182)=k7_relat_1('#skF_5', D_2182))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_32471])).
% 13.95/5.87  tff(c_8114, plain, (![A_622, B_623, C_624, D_625]: (k7_relset_1(A_622, B_623, C_624, D_625)=k9_relat_1(C_624, D_625) | ~m1_subset_1(C_624, k1_zfmisc_1(k2_zfmisc_1(A_622, B_623))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 13.95/5.87  tff(c_8132, plain, (![D_625]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_625)=k9_relat_1('#skF_5', D_625))), inference(resolution, [status(thm)], [c_84, c_8114])).
% 13.95/5.87  tff(c_80, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.95/5.87  tff(c_8228, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8132, c_80])).
% 13.95/5.87  tff(c_40, plain, (![B_23, A_22]: (k2_relat_1(k7_relat_1(B_23, A_22))=k9_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.95/5.87  tff(c_2831, plain, (![C_242, A_243, B_244]: (v4_relat_1(C_242, A_243) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 13.95/5.87  tff(c_2851, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_2831])).
% 13.95/5.87  tff(c_2931, plain, (![C_261, A_262, B_263]: (v1_relat_1(k7_relat_1(C_261, A_262)) | ~v4_relat_1(C_261, B_263) | ~v1_relat_1(C_261))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.95/5.87  tff(c_2939, plain, (![A_262]: (v1_relat_1(k7_relat_1('#skF_5', A_262)) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_2851, c_2931])).
% 13.95/5.87  tff(c_2949, plain, (![A_262]: (v1_relat_1(k7_relat_1('#skF_5', A_262)))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_2939])).
% 13.95/5.87  tff(c_3149, plain, (![C_302, A_303, B_304]: (v4_relat_1(k7_relat_1(C_302, A_303), A_303) | ~v4_relat_1(C_302, B_304) | ~v1_relat_1(C_302))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.95/5.87  tff(c_3159, plain, (![A_303]: (v4_relat_1(k7_relat_1('#skF_5', A_303), A_303) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_2851, c_3149])).
% 13.95/5.87  tff(c_3170, plain, (![A_303]: (v4_relat_1(k7_relat_1('#skF_5', A_303), A_303))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_3159])).
% 13.95/5.87  tff(c_30, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.95/5.87  tff(c_8316, plain, (![C_640, A_641, B_642]: (m1_subset_1(C_640, k1_zfmisc_1(k2_zfmisc_1(A_641, B_642))) | ~r1_tarski(k2_relat_1(C_640), B_642) | ~r1_tarski(k1_relat_1(C_640), A_641) | ~v1_relat_1(C_640))), inference(cnfTransformation, [status(thm)], [f_109])).
% 13.95/5.87  tff(c_8251, plain, (![A_628, B_629, C_630, D_631]: (k2_partfun1(A_628, B_629, C_630, D_631)=k7_relat_1(C_630, D_631) | ~m1_subset_1(C_630, k1_zfmisc_1(k2_zfmisc_1(A_628, B_629))) | ~v1_funct_1(C_630))), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.95/5.87  tff(c_8263, plain, (![D_631]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_631)=k7_relat_1('#skF_5', D_631) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_84, c_8251])).
% 13.95/5.87  tff(c_8273, plain, (![D_631]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_631)=k7_relat_1('#skF_5', D_631))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_8263])).
% 13.95/5.87  tff(c_2749, plain, (![A_232, B_233, C_234, D_235]: (v1_funct_1(k2_partfun1(A_232, B_233, C_234, D_235)) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))) | ~v1_funct_1(C_234))), inference(cnfTransformation, [status(thm)], [f_135])).
% 13.95/5.87  tff(c_2761, plain, (![D_235]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_235)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_84, c_2749])).
% 13.95/5.87  tff(c_2769, plain, (![D_235]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_235)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2761])).
% 13.95/5.87  tff(c_78, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_172])).
% 13.95/5.87  tff(c_160, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_78])).
% 13.95/5.87  tff(c_2772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2769, c_160])).
% 13.95/5.87  tff(c_2773, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_78])).
% 13.95/5.87  tff(c_2775, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_2773])).
% 13.95/5.87  tff(c_8279, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_8273, c_2775])).
% 13.95/5.87  tff(c_8319, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_8316, c_8279])).
% 13.95/5.87  tff(c_8351, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2949, c_8319])).
% 13.95/5.87  tff(c_8368, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(splitLeft, [status(thm)], [c_8351])).
% 13.95/5.87  tff(c_8371, plain, (~v4_relat_1(k7_relat_1('#skF_5', '#skF_2'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_8368])).
% 13.95/5.87  tff(c_8375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2949, c_3170, c_8371])).
% 13.95/5.87  tff(c_8376, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_8351])).
% 13.95/5.87  tff(c_8393, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_40, c_8376])).
% 13.95/5.87  tff(c_8396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_8228, c_8393])).
% 13.95/5.87  tff(c_8398, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_2773])).
% 13.95/5.87  tff(c_31283, plain, (k1_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_8398, c_31258])).
% 13.95/5.87  tff(c_32490, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32485, c_32485, c_31283])).
% 13.95/5.87  tff(c_8397, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_2773])).
% 13.95/5.87  tff(c_32502, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32485, c_8397])).
% 13.95/5.87  tff(c_32501, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32485, c_8398])).
% 13.95/5.87  tff(c_60, plain, (![B_40, C_41, A_39]: (k1_xboole_0=B_40 | v1_funct_2(C_41, A_39, B_40) | k1_relset_1(A_39, B_40, C_41)!=A_39 | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.95/5.87  tff(c_32876, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(resolution, [status(thm)], [c_32501, c_60])).
% 13.95/5.87  tff(c_32905, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_32502, c_32876])).
% 13.95/5.87  tff(c_33462, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32490, c_32905])).
% 13.95/5.87  tff(c_33463, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_33462])).
% 13.95/5.87  tff(c_33466, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32669, c_33463])).
% 13.95/5.87  tff(c_33470, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_33466])).
% 13.95/5.87  tff(c_33471, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_33462])).
% 13.95/5.87  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.95/5.87  tff(c_33538, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_33471, c_10])).
% 13.95/5.87  tff(c_14, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 13.95/5.87  tff(c_33537, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_33471, c_33471, c_14])).
% 13.95/5.87  tff(c_20, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.95/5.87  tff(c_26757, plain, (r1_tarski(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_8398, c_20])).
% 13.95/5.87  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.95/5.87  tff(c_26805, plain, (k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')=k2_zfmisc_1('#skF_2', '#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_26757, c_4])).
% 13.95/5.87  tff(c_26937, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_26805])).
% 13.95/5.87  tff(c_32496, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32485, c_26937])).
% 13.95/5.87  tff(c_33666, plain, (~r1_tarski('#skF_3', k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_33537, c_32496])).
% 13.95/5.87  tff(c_33670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33538, c_33666])).
% 13.95/5.87  tff(c_33671, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_32590])).
% 13.95/5.87  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 13.95/5.87  tff(c_33732, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_33671, c_2])).
% 13.95/5.87  tff(c_33734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_33732])).
% 13.95/5.87  tff(c_33735, plain, (k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')=k2_zfmisc_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_26805])).
% 13.95/5.87  tff(c_35886, plain, (~v1_funct_2(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_33735, c_8397])).
% 13.95/5.87  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.95/5.87  tff(c_22, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.95/5.87  tff(c_39380, plain, (![A_2655, B_2656, C_2657]: (k1_relset_1(A_2655, B_2656, C_2657)=k1_relat_1(C_2657) | ~m1_subset_1(C_2657, k1_zfmisc_1(k2_zfmisc_1(A_2655, B_2656))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 13.95/5.87  tff(c_39595, plain, (![A_2671, B_2672, A_2673]: (k1_relset_1(A_2671, B_2672, A_2673)=k1_relat_1(A_2673) | ~r1_tarski(A_2673, k2_zfmisc_1(A_2671, B_2672)))), inference(resolution, [status(thm)], [c_22, c_39380])).
% 13.95/5.87  tff(c_39622, plain, (![A_2671, B_2672]: (k1_relset_1(A_2671, B_2672, k2_zfmisc_1(A_2671, B_2672))=k1_relat_1(k2_zfmisc_1(A_2671, B_2672)))), inference(resolution, [status(thm)], [c_8, c_39595])).
% 13.95/5.87  tff(c_35885, plain, (m1_subset_1(k2_zfmisc_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_33735, c_8398])).
% 13.95/5.87  tff(c_40669, plain, (![B_2752, C_2753, A_2754]: (k1_xboole_0=B_2752 | v1_funct_2(C_2753, A_2754, B_2752) | k1_relset_1(A_2754, B_2752, C_2753)!=A_2754 | ~m1_subset_1(C_2753, k1_zfmisc_1(k2_zfmisc_1(A_2754, B_2752))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.95/5.87  tff(c_40678, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k2_zfmisc_1('#skF_2', '#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_35885, c_40669])).
% 13.95/5.87  tff(c_40699, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_2', '#skF_3') | k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_39622, c_40678])).
% 13.95/5.87  tff(c_40700, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_35886, c_40699])).
% 13.95/5.87  tff(c_40812, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_40700])).
% 13.95/5.87  tff(c_40162, plain, (![A_2730, B_2731, C_2732, D_2733]: (k2_partfun1(A_2730, B_2731, C_2732, D_2733)=k7_relat_1(C_2732, D_2733) | ~m1_subset_1(C_2732, k1_zfmisc_1(k2_zfmisc_1(A_2730, B_2731))) | ~v1_funct_1(C_2732))), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.95/5.87  tff(c_40176, plain, (![D_2733]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_2733)=k7_relat_1('#skF_5', D_2733) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_84, c_40162])).
% 13.95/5.87  tff(c_40191, plain, (![D_2734]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_2734)=k7_relat_1('#skF_5', D_2734))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_40176])).
% 13.95/5.87  tff(c_40197, plain, (k7_relat_1('#skF_5', '#skF_2')=k2_zfmisc_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_40191, c_33735])).
% 13.95/5.87  tff(c_39409, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_84, c_39380])).
% 13.95/5.87  tff(c_40441, plain, (![B_2747, A_2748, C_2749]: (k1_xboole_0=B_2747 | k1_relset_1(A_2748, B_2747, C_2749)=A_2748 | ~v1_funct_2(C_2749, A_2748, B_2747) | ~m1_subset_1(C_2749, k1_zfmisc_1(k2_zfmisc_1(A_2748, B_2747))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.95/5.87  tff(c_40464, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_84, c_40441])).
% 13.95/5.87  tff(c_40477, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_39409, c_40464])).
% 13.95/5.87  tff(c_40479, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_40477])).
% 13.95/5.87  tff(c_40512, plain, (![A_24]: (k1_relat_1(k7_relat_1('#skF_5', A_24))=A_24 | ~r1_tarski(A_24, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_40479, c_42])).
% 13.95/5.87  tff(c_41104, plain, (![A_2770]: (k1_relat_1(k7_relat_1('#skF_5', A_2770))=A_2770 | ~r1_tarski(A_2770, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_40512])).
% 13.95/5.87  tff(c_41172, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))='#skF_2' | ~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_40197, c_41104])).
% 13.95/5.87  tff(c_41226, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_41172])).
% 13.95/5.87  tff(c_41228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40812, c_41226])).
% 13.95/5.87  tff(c_41229, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_40700])).
% 13.95/5.87  tff(c_100, plain, (![A_56]: (k2_zfmisc_1(A_56, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 13.95/5.87  tff(c_104, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_100, c_38])).
% 13.95/5.87  tff(c_18, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 13.95/5.87  tff(c_26696, plain, (![C_1752, A_1753, B_1754]: (v4_relat_1(C_1752, A_1753) | ~m1_subset_1(C_1752, k1_zfmisc_1(k2_zfmisc_1(A_1753, B_1754))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 13.95/5.87  tff(c_26717, plain, (![A_1755]: (v4_relat_1(k1_xboole_0, A_1755))), inference(resolution, [status(thm)], [c_18, c_26696])).
% 13.95/5.87  tff(c_26678, plain, (![B_1749, A_1750]: (r1_tarski(k1_relat_1(B_1749), A_1750) | ~v4_relat_1(B_1749, A_1750) | ~v1_relat_1(B_1749))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.95/5.87  tff(c_8435, plain, (![B_648, A_649]: (B_648=A_649 | ~r1_tarski(B_648, A_649) | ~r1_tarski(A_649, B_648))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.95/5.87  tff(c_8448, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_8435])).
% 13.95/5.87  tff(c_26692, plain, (![B_1749]: (k1_relat_1(B_1749)=k1_xboole_0 | ~v4_relat_1(B_1749, k1_xboole_0) | ~v1_relat_1(B_1749))), inference(resolution, [status(thm)], [c_26678, c_8448])).
% 13.95/5.87  tff(c_26721, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_26717, c_26692])).
% 13.95/5.87  tff(c_26724, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_104, c_26721])).
% 13.95/5.87  tff(c_39394, plain, (![A_2655, B_2656]: (k1_relset_1(A_2655, B_2656, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_39380])).
% 13.95/5.87  tff(c_39408, plain, (![A_2655, B_2656]: (k1_relset_1(A_2655, B_2656, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26724, c_39394])).
% 13.95/5.87  tff(c_16, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 13.95/5.87  tff(c_58, plain, (![C_41, B_40]: (v1_funct_2(C_41, k1_xboole_0, B_40) | k1_relset_1(k1_xboole_0, B_40, C_41)!=k1_xboole_0 | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_40))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 13.95/5.87  tff(c_39522, plain, (![C_2660, B_2661]: (v1_funct_2(C_2660, k1_xboole_0, B_2661) | k1_relset_1(k1_xboole_0, B_2661, C_2660)!=k1_xboole_0 | ~m1_subset_1(C_2660, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_58])).
% 13.95/5.87  tff(c_39528, plain, (![B_2661]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_2661) | k1_relset_1(k1_xboole_0, B_2661, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_39522])).
% 13.95/5.87  tff(c_39532, plain, (![B_2661]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_2661))), inference(demodulation, [status(thm), theory('equality')], [c_39408, c_39528])).
% 13.95/5.87  tff(c_41253, plain, (![B_2661]: (v1_funct_2('#skF_3', '#skF_3', B_2661))), inference(demodulation, [status(thm), theory('equality')], [c_41229, c_41229, c_39532])).
% 13.95/5.87  tff(c_41273, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_41229, c_41229, c_26724])).
% 13.95/5.87  tff(c_41282, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_41229, c_41229, c_14])).
% 13.95/5.87  tff(c_41230, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_40700])).
% 13.95/5.87  tff(c_42030, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_41273, c_41282, c_41230])).
% 13.95/5.87  tff(c_41686, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_41282, c_35886])).
% 13.95/5.87  tff(c_42032, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42030, c_41686])).
% 13.95/5.87  tff(c_42040, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41253, c_42032])).
% 13.95/5.87  tff(c_42041, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_40477])).
% 13.95/5.87  tff(c_42093, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42041, c_2])).
% 13.95/5.87  tff(c_42095, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_42093])).
% 13.95/5.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.95/5.87  
% 13.95/5.87  Inference rules
% 13.95/5.87  ----------------------
% 13.95/5.87  #Ref     : 0
% 13.95/5.87  #Sup     : 9076
% 13.95/5.87  #Fact    : 0
% 13.95/5.87  #Define  : 0
% 13.95/5.87  #Split   : 117
% 13.95/5.87  #Chain   : 0
% 13.95/5.87  #Close   : 0
% 13.95/5.87  
% 13.95/5.87  Ordering : KBO
% 13.95/5.87  
% 13.95/5.87  Simplification rules
% 13.95/5.87  ----------------------
% 13.95/5.87  #Subsume      : 1226
% 13.95/5.87  #Demod        : 10559
% 13.95/5.87  #Tautology    : 4284
% 13.95/5.87  #SimpNegUnit  : 240
% 13.95/5.87  #BackRed      : 977
% 13.95/5.87  
% 13.95/5.87  #Partial instantiations: 0
% 13.95/5.87  #Strategies tried      : 1
% 13.95/5.87  
% 13.95/5.87  Timing (in seconds)
% 13.95/5.87  ----------------------
% 13.95/5.87  Preprocessing        : 0.36
% 13.95/5.87  Parsing              : 0.19
% 13.95/5.87  CNF conversion       : 0.03
% 13.95/5.87  Main loop            : 4.70
% 13.95/5.87  Inferencing          : 1.33
% 13.95/5.87  Reduction            : 1.93
% 13.95/5.88  Demodulation         : 1.43
% 13.95/5.88  BG Simplification    : 0.13
% 13.95/5.88  Subsumption          : 0.97
% 13.95/5.88  Abstraction          : 0.16
% 13.95/5.88  MUC search           : 0.00
% 13.95/5.88  Cooper               : 0.00
% 13.95/5.88  Total                : 5.12
% 13.95/5.88  Index Insertion      : 0.00
% 13.95/5.88  Index Deletion       : 0.00
% 13.95/5.88  Index Matching       : 0.00
% 13.95/5.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
