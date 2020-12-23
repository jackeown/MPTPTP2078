%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:39 EST 2020

% Result     : Theorem 7.23s
% Output     : CNFRefutation 7.39s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 409 expanded)
%              Number of leaves         :   41 ( 155 expanded)
%              Depth                    :   11
%              Number of atoms          :  226 (1087 expanded)
%              Number of equality atoms :   24 ( 228 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_161,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

tff(f_70,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_135,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_152,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(c_100,plain,(
    r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1631,plain,(
    ! [A_339,B_340,D_341] :
      ( '#skF_6'(A_339,B_340,k1_funct_2(A_339,B_340),D_341) = D_341
      | ~ r2_hidden(D_341,k1_funct_2(A_339,B_340)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1650,plain,(
    '#skF_6'('#skF_8','#skF_9',k1_funct_2('#skF_8','#skF_9'),'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_100,c_1631])).

tff(c_1689,plain,(
    ! [A_345,B_346,D_347] :
      ( v1_relat_1('#skF_6'(A_345,B_346,k1_funct_2(A_345,B_346),D_347))
      | ~ r2_hidden(D_347,k1_funct_2(A_345,B_346)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1692,plain,
    ( v1_relat_1('#skF_10')
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1650,c_1689])).

tff(c_1694,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1692])).

tff(c_98,plain,
    ( ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9')))
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_121,plain,(
    ~ v1_funct_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_317,plain,(
    ! [A_131,B_132,D_133] :
      ( '#skF_6'(A_131,B_132,k1_funct_2(A_131,B_132),D_133) = D_133
      | ~ r2_hidden(D_133,k1_funct_2(A_131,B_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_336,plain,(
    '#skF_6'('#skF_8','#skF_9',k1_funct_2('#skF_8','#skF_9'),'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_100,c_317])).

tff(c_346,plain,(
    ! [A_134,B_135,D_136] :
      ( v1_funct_1('#skF_6'(A_134,B_135,k1_funct_2(A_134,B_135),D_136))
      | ~ r2_hidden(D_136,k1_funct_2(A_134,B_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_349,plain,
    ( v1_funct_1('#skF_10')
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_346])).

tff(c_351,plain,(
    v1_funct_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_349])).

tff(c_353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_351])).

tff(c_355,plain,(
    v1_funct_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_1700,plain,(
    ! [A_350,B_351,D_352] :
      ( k1_relat_1('#skF_6'(A_350,B_351,k1_funct_2(A_350,B_351),D_352)) = A_350
      | ~ r2_hidden(D_352,k1_funct_2(A_350,B_351)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1728,plain,
    ( k1_relat_1('#skF_10') = '#skF_8'
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1650,c_1700])).

tff(c_1732,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1728])).

tff(c_1538,plain,(
    ! [A_315,B_316] :
      ( k1_funct_1(A_315,B_316) = k1_xboole_0
      | r2_hidden(B_316,k1_relat_1(A_315))
      | ~ v1_funct_1(A_315)
      | ~ v1_relat_1(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1550,plain,(
    ! [A_315,B_316] :
      ( ~ v1_xboole_0(k1_relat_1(A_315))
      | k1_funct_1(A_315,B_316) = k1_xboole_0
      | ~ v1_funct_1(A_315)
      | ~ v1_relat_1(A_315) ) ),
    inference(resolution,[status(thm)],[c_1538,c_2])).

tff(c_1740,plain,(
    ! [B_316] :
      ( ~ v1_xboole_0('#skF_8')
      | k1_funct_1('#skF_10',B_316) = k1_xboole_0
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1732,c_1550])).

tff(c_1760,plain,(
    ! [B_316] :
      ( ~ v1_xboole_0('#skF_8')
      | k1_funct_1('#skF_10',B_316) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1694,c_355,c_1740])).

tff(c_1770,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1760])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1507,plain,(
    ! [A_302] :
      ( m1_subset_1(A_302,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_302),k2_relat_1(A_302))))
      | ~ v1_funct_1(A_302)
      | ~ v1_relat_1(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1515,plain,(
    ! [A_302] :
      ( r1_tarski(A_302,k2_zfmisc_1(k1_relat_1(A_302),k2_relat_1(A_302)))
      | ~ v1_funct_1(A_302)
      | ~ v1_relat_1(A_302) ) ),
    inference(resolution,[status(thm)],[c_1507,c_18])).

tff(c_1743,plain,
    ( r1_tarski('#skF_10',k2_zfmisc_1('#skF_8',k2_relat_1('#skF_10')))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_1732,c_1515])).

tff(c_1762,plain,(
    r1_tarski('#skF_10',k2_zfmisc_1('#skF_8',k2_relat_1('#skF_10'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1694,c_355,c_1743])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1481,plain,(
    ! [C_296,B_297,A_298] :
      ( v1_xboole_0(C_296)
      | ~ m1_subset_1(C_296,k1_zfmisc_1(k2_zfmisc_1(B_297,A_298)))
      | ~ v1_xboole_0(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1490,plain,(
    ! [A_12,A_298,B_297] :
      ( v1_xboole_0(A_12)
      | ~ v1_xboole_0(A_298)
      | ~ r1_tarski(A_12,k2_zfmisc_1(B_297,A_298)) ) ),
    inference(resolution,[status(thm)],[c_20,c_1481])).

tff(c_1788,plain,
    ( v1_xboole_0('#skF_10')
    | ~ v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_1762,c_1490])).

tff(c_1792,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_1788])).

tff(c_562,plain,(
    ! [A_201,B_202,D_203] :
      ( '#skF_6'(A_201,B_202,k1_funct_2(A_201,B_202),D_203) = D_203
      | ~ r2_hidden(D_203,k1_funct_2(A_201,B_202)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_581,plain,(
    '#skF_6'('#skF_8','#skF_9',k1_funct_2('#skF_8','#skF_9'),'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_100,c_562])).

tff(c_54,plain,(
    ! [A_34,B_35,D_50] :
      ( v1_relat_1('#skF_6'(A_34,B_35,k1_funct_2(A_34,B_35),D_50))
      | ~ r2_hidden(D_50,k1_funct_2(A_34,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_585,plain,
    ( v1_relat_1('#skF_10')
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_54])).

tff(c_592,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_585])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_602,plain,(
    ! [A_208,B_209,D_210] :
      ( k1_relat_1('#skF_6'(A_208,B_209,k1_funct_2(A_208,B_209),D_210)) = A_208
      | ~ r2_hidden(D_210,k1_funct_2(A_208,B_209)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_630,plain,
    ( k1_relat_1('#skF_10') = '#skF_8'
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_602])).

tff(c_634,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_630])).

tff(c_754,plain,(
    ! [A_215,B_216,D_217] :
      ( r1_tarski(k2_relat_1('#skF_6'(A_215,B_216,k1_funct_2(A_215,B_216),D_217)),B_216)
      | ~ r2_hidden(D_217,k1_funct_2(A_215,B_216)) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_773,plain,
    ( r1_tarski(k2_relat_1('#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_10',k1_funct_2('#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_581,c_754])).

tff(c_781,plain,(
    r1_tarski(k2_relat_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_773])).

tff(c_1438,plain,(
    ! [C_292,A_293,B_294] :
      ( m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_293,B_294)))
      | ~ r1_tarski(k2_relat_1(C_292),B_294)
      | ~ r1_tarski(k1_relat_1(C_292),A_293)
      | ~ v1_relat_1(C_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_354,plain,
    ( ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_428,plain,(
    ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_354])).

tff(c_1447,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_10'),'#skF_9')
    | ~ r1_tarski(k1_relat_1('#skF_10'),'#skF_8')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_1438,c_428])).

tff(c_1456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_592,c_16,c_634,c_781,c_1447])).

tff(c_1457,plain,(
    ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_354])).

tff(c_1458,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_354])).

tff(c_1925,plain,(
    ! [C_370,A_371,B_372] :
      ( v1_funct_2(C_370,A_371,B_372)
      | ~ v1_partfun1(C_370,A_371)
      | ~ v1_funct_1(C_370)
      | ~ m1_subset_1(C_370,k1_zfmisc_1(k2_zfmisc_1(A_371,B_372))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1934,plain,
    ( v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ v1_partfun1('#skF_10','#skF_8')
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_1458,c_1925])).

tff(c_1945,plain,
    ( v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ v1_partfun1('#skF_10','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_1934])).

tff(c_1946,plain,(
    ~ v1_partfun1('#skF_10','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_1457,c_1945])).

tff(c_82,plain,(
    ! [A_54] :
      ( v1_funct_2(A_54,k1_relat_1(A_54),k2_relat_1(A_54))
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1752,plain,
    ( v1_funct_2('#skF_10','#skF_8',k2_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_1732,c_82])).

tff(c_1768,plain,(
    v1_funct_2('#skF_10','#skF_8',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1694,c_355,c_1752])).

tff(c_80,plain,(
    ! [A_54] :
      ( m1_subset_1(A_54,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_54),k2_relat_1(A_54))))
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1749,plain,
    ( m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k2_relat_1('#skF_10'))))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_1732,c_80])).

tff(c_1766,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8',k2_relat_1('#skF_10')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1694,c_355,c_1749])).

tff(c_2868,plain,(
    ! [C_460,A_461,B_462] :
      ( v1_partfun1(C_460,A_461)
      | ~ v1_funct_2(C_460,A_461,B_462)
      | ~ v1_funct_1(C_460)
      | ~ m1_subset_1(C_460,k1_zfmisc_1(k2_zfmisc_1(A_461,B_462)))
      | v1_xboole_0(B_462) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2874,plain,
    ( v1_partfun1('#skF_10','#skF_8')
    | ~ v1_funct_2('#skF_10','#skF_8',k2_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_1766,c_2868])).

tff(c_2888,plain,
    ( v1_partfun1('#skF_10','#skF_8')
    | v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_355,c_1768,c_2874])).

tff(c_2890,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1792,c_1946,c_2888])).

tff(c_2891,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_1788])).

tff(c_3380,plain,(
    ! [B_497,A_498] :
      ( r2_hidden(k4_tarski(B_497,k1_funct_1(A_498,B_497)),A_498)
      | ~ r2_hidden(B_497,k1_relat_1(A_498))
      | ~ v1_funct_1(A_498)
      | ~ v1_relat_1(A_498) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3397,plain,(
    ! [A_499,B_500] :
      ( ~ v1_xboole_0(A_499)
      | ~ r2_hidden(B_500,k1_relat_1(A_499))
      | ~ v1_funct_1(A_499)
      | ~ v1_relat_1(A_499) ) ),
    inference(resolution,[status(thm)],[c_3380,c_2])).

tff(c_3416,plain,(
    ! [B_500] :
      ( ~ v1_xboole_0('#skF_10')
      | ~ r2_hidden(B_500,'#skF_8')
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1732,c_3397])).

tff(c_3451,plain,(
    ! [B_501] : ~ r2_hidden(B_501,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1694,c_355,c_2891,c_3416])).

tff(c_3483,plain,(
    v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_4,c_3451])).

tff(c_3496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1770,c_3483])).

tff(c_3498,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1760])).

tff(c_6713,plain,(
    ! [C_757,B_758] :
      ( r2_hidden('#skF_7'(k1_relat_1(C_757),B_758,C_757),k1_relat_1(C_757))
      | v1_funct_2(C_757,k1_relat_1(C_757),B_758)
      | ~ v1_funct_1(C_757)
      | ~ v1_relat_1(C_757) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_6730,plain,(
    ! [B_758] :
      ( r2_hidden('#skF_7'('#skF_8',B_758,'#skF_10'),k1_relat_1('#skF_10'))
      | v1_funct_2('#skF_10',k1_relat_1('#skF_10'),B_758)
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1732,c_6713])).

tff(c_6824,plain,(
    ! [B_760] :
      ( r2_hidden('#skF_7'('#skF_8',B_760,'#skF_10'),'#skF_8')
      | v1_funct_2('#skF_10','#skF_8',B_760) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1694,c_355,c_1732,c_1732,c_6730])).

tff(c_6829,plain,(
    ! [B_760] :
      ( ~ v1_xboole_0('#skF_8')
      | v1_funct_2('#skF_10','#skF_8',B_760) ) ),
    inference(resolution,[status(thm)],[c_6824,c_2])).

tff(c_6833,plain,(
    ! [B_760] : v1_funct_2('#skF_10','#skF_8',B_760) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3498,c_6829])).

tff(c_6838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6833,c_1457])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:32:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.23/2.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.39/2.59  
% 7.39/2.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.39/2.59  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_2
% 7.39/2.59  
% 7.39/2.59  %Foreground sorts:
% 7.39/2.59  
% 7.39/2.59  
% 7.39/2.59  %Background operators:
% 7.39/2.59  
% 7.39/2.59  
% 7.39/2.59  %Foreground operators:
% 7.39/2.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.39/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.39/2.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.39/2.59  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.39/2.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.39/2.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.39/2.59  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.39/2.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.39/2.59  tff('#skF_10', type, '#skF_10': $i).
% 7.39/2.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.39/2.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.39/2.59  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.39/2.59  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.39/2.59  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 7.39/2.59  tff('#skF_9', type, '#skF_9': $i).
% 7.39/2.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.39/2.59  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 7.39/2.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.39/2.59  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 7.39/2.59  tff('#skF_8', type, '#skF_8': $i).
% 7.39/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.39/2.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.39/2.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.39/2.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.39/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.39/2.59  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.39/2.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.39/2.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.39/2.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.39/2.59  
% 7.39/2.61  tff(f_161, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 7.39/2.61  tff(f_125, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 7.39/2.61  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 7.39/2.61  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.39/2.61  tff(f_135, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 7.39/2.61  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.39/2.61  tff(f_77, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 7.39/2.61  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.39/2.61  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 7.39/2.61  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 7.39/2.61  tff(f_109, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 7.39/2.61  tff(f_152, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 7.39/2.61  tff(c_100, plain, (r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.39/2.61  tff(c_1631, plain, (![A_339, B_340, D_341]: ('#skF_6'(A_339, B_340, k1_funct_2(A_339, B_340), D_341)=D_341 | ~r2_hidden(D_341, k1_funct_2(A_339, B_340)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.39/2.61  tff(c_1650, plain, ('#skF_6'('#skF_8', '#skF_9', k1_funct_2('#skF_8', '#skF_9'), '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_100, c_1631])).
% 7.39/2.61  tff(c_1689, plain, (![A_345, B_346, D_347]: (v1_relat_1('#skF_6'(A_345, B_346, k1_funct_2(A_345, B_346), D_347)) | ~r2_hidden(D_347, k1_funct_2(A_345, B_346)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.39/2.61  tff(c_1692, plain, (v1_relat_1('#skF_10') | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1650, c_1689])).
% 7.39/2.61  tff(c_1694, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1692])).
% 7.39/2.61  tff(c_98, plain, (~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9'))) | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.39/2.61  tff(c_121, plain, (~v1_funct_1('#skF_10')), inference(splitLeft, [status(thm)], [c_98])).
% 7.39/2.61  tff(c_317, plain, (![A_131, B_132, D_133]: ('#skF_6'(A_131, B_132, k1_funct_2(A_131, B_132), D_133)=D_133 | ~r2_hidden(D_133, k1_funct_2(A_131, B_132)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.39/2.61  tff(c_336, plain, ('#skF_6'('#skF_8', '#skF_9', k1_funct_2('#skF_8', '#skF_9'), '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_100, c_317])).
% 7.39/2.61  tff(c_346, plain, (![A_134, B_135, D_136]: (v1_funct_1('#skF_6'(A_134, B_135, k1_funct_2(A_134, B_135), D_136)) | ~r2_hidden(D_136, k1_funct_2(A_134, B_135)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.39/2.61  tff(c_349, plain, (v1_funct_1('#skF_10') | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_336, c_346])).
% 7.39/2.61  tff(c_351, plain, (v1_funct_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_349])).
% 7.39/2.61  tff(c_353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_351])).
% 7.39/2.61  tff(c_355, plain, (v1_funct_1('#skF_10')), inference(splitRight, [status(thm)], [c_98])).
% 7.39/2.61  tff(c_1700, plain, (![A_350, B_351, D_352]: (k1_relat_1('#skF_6'(A_350, B_351, k1_funct_2(A_350, B_351), D_352))=A_350 | ~r2_hidden(D_352, k1_funct_2(A_350, B_351)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.39/2.61  tff(c_1728, plain, (k1_relat_1('#skF_10')='#skF_8' | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1650, c_1700])).
% 7.39/2.61  tff(c_1732, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1728])).
% 7.39/2.61  tff(c_1538, plain, (![A_315, B_316]: (k1_funct_1(A_315, B_316)=k1_xboole_0 | r2_hidden(B_316, k1_relat_1(A_315)) | ~v1_funct_1(A_315) | ~v1_relat_1(A_315))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.39/2.61  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.39/2.61  tff(c_1550, plain, (![A_315, B_316]: (~v1_xboole_0(k1_relat_1(A_315)) | k1_funct_1(A_315, B_316)=k1_xboole_0 | ~v1_funct_1(A_315) | ~v1_relat_1(A_315))), inference(resolution, [status(thm)], [c_1538, c_2])).
% 7.39/2.61  tff(c_1740, plain, (![B_316]: (~v1_xboole_0('#skF_8') | k1_funct_1('#skF_10', B_316)=k1_xboole_0 | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1732, c_1550])).
% 7.39/2.61  tff(c_1760, plain, (![B_316]: (~v1_xboole_0('#skF_8') | k1_funct_1('#skF_10', B_316)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1694, c_355, c_1740])).
% 7.39/2.61  tff(c_1770, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_1760])).
% 7.39/2.61  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.39/2.61  tff(c_1507, plain, (![A_302]: (m1_subset_1(A_302, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_302), k2_relat_1(A_302)))) | ~v1_funct_1(A_302) | ~v1_relat_1(A_302))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.39/2.61  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.39/2.61  tff(c_1515, plain, (![A_302]: (r1_tarski(A_302, k2_zfmisc_1(k1_relat_1(A_302), k2_relat_1(A_302))) | ~v1_funct_1(A_302) | ~v1_relat_1(A_302))), inference(resolution, [status(thm)], [c_1507, c_18])).
% 7.39/2.61  tff(c_1743, plain, (r1_tarski('#skF_10', k2_zfmisc_1('#skF_8', k2_relat_1('#skF_10'))) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_1732, c_1515])).
% 7.39/2.61  tff(c_1762, plain, (r1_tarski('#skF_10', k2_zfmisc_1('#skF_8', k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_1694, c_355, c_1743])).
% 7.39/2.61  tff(c_20, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.39/2.61  tff(c_1481, plain, (![C_296, B_297, A_298]: (v1_xboole_0(C_296) | ~m1_subset_1(C_296, k1_zfmisc_1(k2_zfmisc_1(B_297, A_298))) | ~v1_xboole_0(A_298))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.39/2.61  tff(c_1490, plain, (![A_12, A_298, B_297]: (v1_xboole_0(A_12) | ~v1_xboole_0(A_298) | ~r1_tarski(A_12, k2_zfmisc_1(B_297, A_298)))), inference(resolution, [status(thm)], [c_20, c_1481])).
% 7.39/2.61  tff(c_1788, plain, (v1_xboole_0('#skF_10') | ~v1_xboole_0(k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_1762, c_1490])).
% 7.39/2.61  tff(c_1792, plain, (~v1_xboole_0(k2_relat_1('#skF_10'))), inference(splitLeft, [status(thm)], [c_1788])).
% 7.39/2.61  tff(c_562, plain, (![A_201, B_202, D_203]: ('#skF_6'(A_201, B_202, k1_funct_2(A_201, B_202), D_203)=D_203 | ~r2_hidden(D_203, k1_funct_2(A_201, B_202)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.39/2.61  tff(c_581, plain, ('#skF_6'('#skF_8', '#skF_9', k1_funct_2('#skF_8', '#skF_9'), '#skF_10')='#skF_10'), inference(resolution, [status(thm)], [c_100, c_562])).
% 7.39/2.61  tff(c_54, plain, (![A_34, B_35, D_50]: (v1_relat_1('#skF_6'(A_34, B_35, k1_funct_2(A_34, B_35), D_50)) | ~r2_hidden(D_50, k1_funct_2(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.39/2.61  tff(c_585, plain, (v1_relat_1('#skF_10') | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_581, c_54])).
% 7.39/2.61  tff(c_592, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_585])).
% 7.39/2.61  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.39/2.61  tff(c_602, plain, (![A_208, B_209, D_210]: (k1_relat_1('#skF_6'(A_208, B_209, k1_funct_2(A_208, B_209), D_210))=A_208 | ~r2_hidden(D_210, k1_funct_2(A_208, B_209)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.39/2.61  tff(c_630, plain, (k1_relat_1('#skF_10')='#skF_8' | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_581, c_602])).
% 7.39/2.61  tff(c_634, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_630])).
% 7.39/2.61  tff(c_754, plain, (![A_215, B_216, D_217]: (r1_tarski(k2_relat_1('#skF_6'(A_215, B_216, k1_funct_2(A_215, B_216), D_217)), B_216) | ~r2_hidden(D_217, k1_funct_2(A_215, B_216)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.39/2.61  tff(c_773, plain, (r1_tarski(k2_relat_1('#skF_10'), '#skF_9') | ~r2_hidden('#skF_10', k1_funct_2('#skF_8', '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_581, c_754])).
% 7.39/2.61  tff(c_781, plain, (r1_tarski(k2_relat_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_773])).
% 7.39/2.61  tff(c_1438, plain, (![C_292, A_293, B_294]: (m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_293, B_294))) | ~r1_tarski(k2_relat_1(C_292), B_294) | ~r1_tarski(k1_relat_1(C_292), A_293) | ~v1_relat_1(C_292))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.39/2.61  tff(c_354, plain, (~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(splitRight, [status(thm)], [c_98])).
% 7.39/2.61  tff(c_428, plain, (~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(splitLeft, [status(thm)], [c_354])).
% 7.39/2.61  tff(c_1447, plain, (~r1_tarski(k2_relat_1('#skF_10'), '#skF_9') | ~r1_tarski(k1_relat_1('#skF_10'), '#skF_8') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_1438, c_428])).
% 7.39/2.61  tff(c_1456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_592, c_16, c_634, c_781, c_1447])).
% 7.39/2.61  tff(c_1457, plain, (~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_354])).
% 7.39/2.61  tff(c_1458, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(splitRight, [status(thm)], [c_354])).
% 7.39/2.61  tff(c_1925, plain, (![C_370, A_371, B_372]: (v1_funct_2(C_370, A_371, B_372) | ~v1_partfun1(C_370, A_371) | ~v1_funct_1(C_370) | ~m1_subset_1(C_370, k1_zfmisc_1(k2_zfmisc_1(A_371, B_372))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.39/2.61  tff(c_1934, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_partfun1('#skF_10', '#skF_8') | ~v1_funct_1('#skF_10')), inference(resolution, [status(thm)], [c_1458, c_1925])).
% 7.39/2.61  tff(c_1945, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_partfun1('#skF_10', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_355, c_1934])).
% 7.39/2.61  tff(c_1946, plain, (~v1_partfun1('#skF_10', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_1457, c_1945])).
% 7.39/2.61  tff(c_82, plain, (![A_54]: (v1_funct_2(A_54, k1_relat_1(A_54), k2_relat_1(A_54)) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.39/2.61  tff(c_1752, plain, (v1_funct_2('#skF_10', '#skF_8', k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_1732, c_82])).
% 7.39/2.61  tff(c_1768, plain, (v1_funct_2('#skF_10', '#skF_8', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1694, c_355, c_1752])).
% 7.39/2.61  tff(c_80, plain, (![A_54]: (m1_subset_1(A_54, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_54), k2_relat_1(A_54)))) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.39/2.61  tff(c_1749, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k2_relat_1('#skF_10')))) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_1732, c_80])).
% 7.39/2.61  tff(c_1766, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', k2_relat_1('#skF_10'))))), inference(demodulation, [status(thm), theory('equality')], [c_1694, c_355, c_1749])).
% 7.39/2.61  tff(c_2868, plain, (![C_460, A_461, B_462]: (v1_partfun1(C_460, A_461) | ~v1_funct_2(C_460, A_461, B_462) | ~v1_funct_1(C_460) | ~m1_subset_1(C_460, k1_zfmisc_1(k2_zfmisc_1(A_461, B_462))) | v1_xboole_0(B_462))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.39/2.61  tff(c_2874, plain, (v1_partfun1('#skF_10', '#skF_8') | ~v1_funct_2('#skF_10', '#skF_8', k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | v1_xboole_0(k2_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_1766, c_2868])).
% 7.39/2.61  tff(c_2888, plain, (v1_partfun1('#skF_10', '#skF_8') | v1_xboole_0(k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_355, c_1768, c_2874])).
% 7.39/2.61  tff(c_2890, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1792, c_1946, c_2888])).
% 7.39/2.61  tff(c_2891, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_1788])).
% 7.39/2.61  tff(c_3380, plain, (![B_497, A_498]: (r2_hidden(k4_tarski(B_497, k1_funct_1(A_498, B_497)), A_498) | ~r2_hidden(B_497, k1_relat_1(A_498)) | ~v1_funct_1(A_498) | ~v1_relat_1(A_498))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.39/2.61  tff(c_3397, plain, (![A_499, B_500]: (~v1_xboole_0(A_499) | ~r2_hidden(B_500, k1_relat_1(A_499)) | ~v1_funct_1(A_499) | ~v1_relat_1(A_499))), inference(resolution, [status(thm)], [c_3380, c_2])).
% 7.39/2.61  tff(c_3416, plain, (![B_500]: (~v1_xboole_0('#skF_10') | ~r2_hidden(B_500, '#skF_8') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1732, c_3397])).
% 7.39/2.61  tff(c_3451, plain, (![B_501]: (~r2_hidden(B_501, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1694, c_355, c_2891, c_3416])).
% 7.39/2.61  tff(c_3483, plain, (v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_4, c_3451])).
% 7.39/2.61  tff(c_3496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1770, c_3483])).
% 7.39/2.61  tff(c_3498, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_1760])).
% 7.39/2.61  tff(c_6713, plain, (![C_757, B_758]: (r2_hidden('#skF_7'(k1_relat_1(C_757), B_758, C_757), k1_relat_1(C_757)) | v1_funct_2(C_757, k1_relat_1(C_757), B_758) | ~v1_funct_1(C_757) | ~v1_relat_1(C_757))), inference(cnfTransformation, [status(thm)], [f_152])).
% 7.39/2.61  tff(c_6730, plain, (![B_758]: (r2_hidden('#skF_7'('#skF_8', B_758, '#skF_10'), k1_relat_1('#skF_10')) | v1_funct_2('#skF_10', k1_relat_1('#skF_10'), B_758) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1732, c_6713])).
% 7.39/2.61  tff(c_6824, plain, (![B_760]: (r2_hidden('#skF_7'('#skF_8', B_760, '#skF_10'), '#skF_8') | v1_funct_2('#skF_10', '#skF_8', B_760))), inference(demodulation, [status(thm), theory('equality')], [c_1694, c_355, c_1732, c_1732, c_6730])).
% 7.39/2.61  tff(c_6829, plain, (![B_760]: (~v1_xboole_0('#skF_8') | v1_funct_2('#skF_10', '#skF_8', B_760))), inference(resolution, [status(thm)], [c_6824, c_2])).
% 7.39/2.61  tff(c_6833, plain, (![B_760]: (v1_funct_2('#skF_10', '#skF_8', B_760))), inference(demodulation, [status(thm), theory('equality')], [c_3498, c_6829])).
% 7.39/2.61  tff(c_6838, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6833, c_1457])).
% 7.39/2.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.39/2.61  
% 7.39/2.61  Inference rules
% 7.39/2.61  ----------------------
% 7.39/2.61  #Ref     : 0
% 7.39/2.61  #Sup     : 1584
% 7.39/2.61  #Fact    : 0
% 7.39/2.61  #Define  : 0
% 7.39/2.61  #Split   : 58
% 7.39/2.61  #Chain   : 0
% 7.39/2.61  #Close   : 0
% 7.39/2.61  
% 7.39/2.61  Ordering : KBO
% 7.39/2.61  
% 7.39/2.61  Simplification rules
% 7.39/2.61  ----------------------
% 7.39/2.61  #Subsume      : 412
% 7.39/2.61  #Demod        : 469
% 7.39/2.61  #Tautology    : 240
% 7.39/2.61  #SimpNegUnit  : 32
% 7.39/2.61  #BackRed      : 10
% 7.39/2.61  
% 7.39/2.61  #Partial instantiations: 0
% 7.39/2.61  #Strategies tried      : 1
% 7.39/2.61  
% 7.39/2.61  Timing (in seconds)
% 7.39/2.61  ----------------------
% 7.39/2.61  Preprocessing        : 0.36
% 7.39/2.61  Parsing              : 0.17
% 7.39/2.61  CNF conversion       : 0.03
% 7.39/2.61  Main loop            : 1.43
% 7.39/2.61  Inferencing          : 0.49
% 7.39/2.61  Reduction            : 0.38
% 7.39/2.61  Demodulation         : 0.25
% 7.39/2.61  BG Simplification    : 0.06
% 7.39/2.61  Subsumption          : 0.38
% 7.39/2.61  Abstraction          : 0.06
% 7.39/2.61  MUC search           : 0.00
% 7.39/2.61  Cooper               : 0.00
% 7.39/2.61  Total                : 1.83
% 7.39/2.61  Index Insertion      : 0.00
% 7.39/2.61  Index Deletion       : 0.00
% 7.39/2.61  Index Matching       : 0.00
% 7.39/2.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
