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
% DateTime   : Thu Dec  3 10:16:34 EST 2020

% Result     : Theorem 9.91s
% Output     : CNFRefutation 9.91s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 183 expanded)
%              Number of leaves         :   45 (  84 expanded)
%              Depth                    :    9
%              Number of atoms          :  159 ( 437 expanded)
%              Number of equality atoms :   30 (  76 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_3 > #skF_10 > #skF_8 > #skF_13 > #skF_5 > #skF_7 > #skF_9 > #skF_2 > #skF_1 > #skF_12 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_139,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ~ ( r2_hidden(A,D)
          & ! [E,F] :
              ~ ( A = k4_tarski(E,F)
                & r2_hidden(E,B)
                & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_120,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_103,plain,(
    ! [A_74,B_75] :
      ( ~ r2_hidden('#skF_1'(A_74,B_75),B_75)
      | r1_tarski(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_108,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_103])).

tff(c_72,plain,(
    m1_subset_1('#skF_12',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_110,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_119,plain,(
    v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_72,c_110])).

tff(c_34,plain,(
    ! [A_32,B_33,C_34] :
      ( r2_hidden(k4_tarski('#skF_6'(A_32,B_33,C_34),A_32),C_34)
      | ~ r2_hidden(A_32,k9_relat_1(C_34,B_33))
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2458,plain,(
    ! [A_365,B_366,C_367,D_368] :
      ( r2_hidden('#skF_8'(A_365,B_366,C_367,D_368),C_367)
      | ~ r2_hidden(A_365,D_368)
      | ~ m1_subset_1(D_368,k1_zfmisc_1(k2_zfmisc_1(B_366,C_367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2474,plain,(
    ! [A_369] :
      ( r2_hidden('#skF_8'(A_369,'#skF_9','#skF_10','#skF_12'),'#skF_10')
      | ~ r2_hidden(A_369,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_72,c_2458])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_158,plain,(
    ! [C_94,B_95,A_96] :
      ( ~ v1_xboole_0(C_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(C_94))
      | ~ r2_hidden(A_96,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_167,plain,(
    ! [B_9,A_96,A_8] :
      ( ~ v1_xboole_0(B_9)
      | ~ r2_hidden(A_96,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_158])).

tff(c_2482,plain,(
    ! [B_9,A_369] :
      ( ~ v1_xboole_0(B_9)
      | ~ r1_tarski('#skF_10',B_9)
      | ~ r2_hidden(A_369,'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_2474,c_167])).

tff(c_2486,plain,(
    ! [A_370] : ~ r2_hidden(A_370,'#skF_12') ),
    inference(splitLeft,[status(thm)],[c_2482])).

tff(c_2490,plain,(
    ! [A_32,B_33] :
      ( ~ r2_hidden(A_32,k9_relat_1('#skF_12',B_33))
      | ~ v1_relat_1('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_34,c_2486])).

tff(c_2513,plain,(
    ! [A_32,B_33] : ~ r2_hidden(A_32,k9_relat_1('#skF_12',B_33)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_2490])).

tff(c_1146,plain,(
    ! [A_245,B_246,C_247,D_248] :
      ( k7_relset_1(A_245,B_246,C_247,D_248) = k9_relat_1(C_247,D_248)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_245,B_246))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1161,plain,(
    ! [D_248] : k7_relset_1('#skF_9','#skF_10','#skF_12',D_248) = k9_relat_1('#skF_12',D_248) ),
    inference(resolution,[status(thm)],[c_72,c_1146])).

tff(c_70,plain,(
    r2_hidden('#skF_13',k7_relset_1('#skF_9','#skF_10','#skF_12','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1166,plain,(
    r2_hidden('#skF_13',k9_relat_1('#skF_12','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1161,c_70])).

tff(c_2684,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2513,c_1166])).

tff(c_2686,plain,(
    ! [B_378] :
      ( ~ v1_xboole_0(B_378)
      | ~ r1_tarski('#skF_10',B_378) ) ),
    inference(splitRight,[status(thm)],[c_2482])).

tff(c_2696,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_108,c_2686])).

tff(c_74,plain,(
    v1_funct_2('#skF_12','#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_170,plain,(
    ! [A_97,B_98,C_99] :
      ( k1_relset_1(A_97,B_98,C_99) = k1_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_184,plain,(
    k1_relset_1('#skF_9','#skF_10','#skF_12') = k1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_72,c_170])).

tff(c_4169,plain,(
    ! [B_439,A_440,C_441] :
      ( k1_xboole_0 = B_439
      | k1_relset_1(A_440,B_439,C_441) = A_440
      | ~ v1_funct_2(C_441,A_440,B_439)
      | ~ m1_subset_1(C_441,k1_zfmisc_1(k2_zfmisc_1(A_440,B_439))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4184,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_relset_1('#skF_9','#skF_10','#skF_12') = '#skF_9'
    | ~ v1_funct_2('#skF_12','#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_72,c_4169])).

tff(c_4190,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_relat_1('#skF_12') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_184,c_4184])).

tff(c_4191,plain,(
    k1_relat_1('#skF_12') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_4190])).

tff(c_36,plain,(
    ! [A_32,B_33,C_34] :
      ( r2_hidden('#skF_6'(A_32,B_33,C_34),k1_relat_1(C_34))
      | ~ r2_hidden(A_32,k9_relat_1(C_34,B_33))
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4268,plain,(
    ! [A_32,B_33] :
      ( r2_hidden('#skF_6'(A_32,B_33,'#skF_12'),'#skF_9')
      | ~ r2_hidden(A_32,k9_relat_1('#skF_12',B_33))
      | ~ v1_relat_1('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4191,c_36])).

tff(c_4850,plain,(
    ! [A_460,B_461] :
      ( r2_hidden('#skF_6'(A_460,B_461,'#skF_12'),'#skF_9')
      | ~ r2_hidden(A_460,k9_relat_1('#skF_12',B_461)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_4268])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5351,plain,(
    ! [A_483,B_484] :
      ( m1_subset_1('#skF_6'(A_483,B_484,'#skF_12'),'#skF_9')
      | ~ r2_hidden(A_483,k9_relat_1('#skF_12',B_484)) ) ),
    inference(resolution,[status(thm)],[c_4850,c_10])).

tff(c_5396,plain,(
    m1_subset_1('#skF_6'('#skF_13','#skF_11','#skF_12'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_1166,c_5351])).

tff(c_76,plain,(
    v1_funct_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1457,plain,(
    ! [A_272,B_273,C_274] :
      ( r2_hidden(k4_tarski('#skF_6'(A_272,B_273,C_274),A_272),C_274)
      | ~ r2_hidden(A_272,k9_relat_1(C_274,B_273))
      | ~ v1_relat_1(C_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    ! [C_40,A_38,B_39] :
      ( k1_funct_1(C_40,A_38) = B_39
      | ~ r2_hidden(k4_tarski(A_38,B_39),C_40)
      | ~ v1_funct_1(C_40)
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_13641,plain,(
    ! [C_674,A_675,B_676] :
      ( k1_funct_1(C_674,'#skF_6'(A_675,B_676,C_674)) = A_675
      | ~ v1_funct_1(C_674)
      | ~ r2_hidden(A_675,k9_relat_1(C_674,B_676))
      | ~ v1_relat_1(C_674) ) ),
    inference(resolution,[status(thm)],[c_1457,c_40])).

tff(c_13682,plain,
    ( k1_funct_1('#skF_12','#skF_6'('#skF_13','#skF_11','#skF_12')) = '#skF_13'
    | ~ v1_funct_1('#skF_12')
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_1166,c_13641])).

tff(c_13712,plain,(
    k1_funct_1('#skF_12','#skF_6'('#skF_13','#skF_11','#skF_12')) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_76,c_13682])).

tff(c_609,plain,(
    ! [A_175,B_176,C_177] :
      ( r2_hidden('#skF_6'(A_175,B_176,C_177),B_176)
      | ~ r2_hidden(A_175,k9_relat_1(C_177,B_176))
      | ~ v1_relat_1(C_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_15253,plain,(
    ! [A_692,B_693,C_694,B_695] :
      ( r2_hidden('#skF_6'(A_692,B_693,C_694),B_695)
      | ~ r1_tarski(B_693,B_695)
      | ~ r2_hidden(A_692,k9_relat_1(C_694,B_693))
      | ~ v1_relat_1(C_694) ) ),
    inference(resolution,[status(thm)],[c_609,c_2])).

tff(c_68,plain,(
    ! [F_64] :
      ( k1_funct_1('#skF_12',F_64) != '#skF_13'
      | ~ r2_hidden(F_64,'#skF_11')
      | ~ m1_subset_1(F_64,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_15558,plain,(
    ! [A_699,B_700,C_701] :
      ( k1_funct_1('#skF_12','#skF_6'(A_699,B_700,C_701)) != '#skF_13'
      | ~ m1_subset_1('#skF_6'(A_699,B_700,C_701),'#skF_9')
      | ~ r1_tarski(B_700,'#skF_11')
      | ~ r2_hidden(A_699,k9_relat_1(C_701,B_700))
      | ~ v1_relat_1(C_701) ) ),
    inference(resolution,[status(thm)],[c_15253,c_68])).

tff(c_15624,plain,
    ( k1_funct_1('#skF_12','#skF_6'('#skF_13','#skF_11','#skF_12')) != '#skF_13'
    | ~ m1_subset_1('#skF_6'('#skF_13','#skF_11','#skF_12'),'#skF_9')
    | ~ r1_tarski('#skF_11','#skF_11')
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_1166,c_15558])).

tff(c_15664,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_108,c_5396,c_13712,c_15624])).

tff(c_15665,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_4190])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_15674,plain,(
    v1_xboole_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15665,c_8])).

tff(c_15676,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2696,c_15674])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.91/3.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.91/3.36  
% 9.91/3.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.91/3.36  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_3 > #skF_10 > #skF_8 > #skF_13 > #skF_5 > #skF_7 > #skF_9 > #skF_2 > #skF_1 > #skF_12 > #skF_4
% 9.91/3.36  
% 9.91/3.36  %Foreground sorts:
% 9.91/3.36  
% 9.91/3.36  
% 9.91/3.36  %Background operators:
% 9.91/3.36  
% 9.91/3.36  
% 9.91/3.36  %Foreground operators:
% 9.91/3.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.91/3.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.91/3.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.91/3.36  tff('#skF_11', type, '#skF_11': $i).
% 9.91/3.36  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 9.91/3.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.91/3.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.91/3.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.91/3.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.91/3.36  tff('#skF_10', type, '#skF_10': $i).
% 9.91/3.36  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 9.91/3.36  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 9.91/3.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.91/3.36  tff('#skF_13', type, '#skF_13': $i).
% 9.91/3.36  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 9.91/3.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.91/3.36  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 9.91/3.36  tff('#skF_9', type, '#skF_9': $i).
% 9.91/3.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.91/3.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.91/3.36  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.91/3.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.91/3.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.91/3.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.91/3.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.91/3.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.91/3.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.91/3.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.91/3.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.91/3.36  tff('#skF_12', type, '#skF_12': $i).
% 9.91/3.36  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.91/3.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.91/3.36  
% 9.91/3.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.91/3.38  tff(f_139, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 9.91/3.38  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.91/3.38  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 9.91/3.38  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 9.91/3.38  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.91/3.38  tff(f_48, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 9.91/3.38  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 9.91/3.38  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.91/3.38  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.91/3.38  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 9.91/3.38  tff(f_77, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 9.91/3.38  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.91/3.38  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.91/3.38  tff(c_103, plain, (![A_74, B_75]: (~r2_hidden('#skF_1'(A_74, B_75), B_75) | r1_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.91/3.38  tff(c_108, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_103])).
% 9.91/3.38  tff(c_72, plain, (m1_subset_1('#skF_12', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.91/3.38  tff(c_110, plain, (![C_77, A_78, B_79]: (v1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.91/3.38  tff(c_119, plain, (v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_72, c_110])).
% 9.91/3.38  tff(c_34, plain, (![A_32, B_33, C_34]: (r2_hidden(k4_tarski('#skF_6'(A_32, B_33, C_34), A_32), C_34) | ~r2_hidden(A_32, k9_relat_1(C_34, B_33)) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.91/3.38  tff(c_2458, plain, (![A_365, B_366, C_367, D_368]: (r2_hidden('#skF_8'(A_365, B_366, C_367, D_368), C_367) | ~r2_hidden(A_365, D_368) | ~m1_subset_1(D_368, k1_zfmisc_1(k2_zfmisc_1(B_366, C_367))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 9.91/3.38  tff(c_2474, plain, (![A_369]: (r2_hidden('#skF_8'(A_369, '#skF_9', '#skF_10', '#skF_12'), '#skF_10') | ~r2_hidden(A_369, '#skF_12'))), inference(resolution, [status(thm)], [c_72, c_2458])).
% 9.91/3.38  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.91/3.38  tff(c_158, plain, (![C_94, B_95, A_96]: (~v1_xboole_0(C_94) | ~m1_subset_1(B_95, k1_zfmisc_1(C_94)) | ~r2_hidden(A_96, B_95))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.91/3.38  tff(c_167, plain, (![B_9, A_96, A_8]: (~v1_xboole_0(B_9) | ~r2_hidden(A_96, A_8) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_14, c_158])).
% 9.91/3.38  tff(c_2482, plain, (![B_9, A_369]: (~v1_xboole_0(B_9) | ~r1_tarski('#skF_10', B_9) | ~r2_hidden(A_369, '#skF_12'))), inference(resolution, [status(thm)], [c_2474, c_167])).
% 9.91/3.38  tff(c_2486, plain, (![A_370]: (~r2_hidden(A_370, '#skF_12'))), inference(splitLeft, [status(thm)], [c_2482])).
% 9.91/3.38  tff(c_2490, plain, (![A_32, B_33]: (~r2_hidden(A_32, k9_relat_1('#skF_12', B_33)) | ~v1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_34, c_2486])).
% 9.91/3.38  tff(c_2513, plain, (![A_32, B_33]: (~r2_hidden(A_32, k9_relat_1('#skF_12', B_33)))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_2490])).
% 9.91/3.38  tff(c_1146, plain, (![A_245, B_246, C_247, D_248]: (k7_relset_1(A_245, B_246, C_247, D_248)=k9_relat_1(C_247, D_248) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_245, B_246))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.91/3.38  tff(c_1161, plain, (![D_248]: (k7_relset_1('#skF_9', '#skF_10', '#skF_12', D_248)=k9_relat_1('#skF_12', D_248))), inference(resolution, [status(thm)], [c_72, c_1146])).
% 9.91/3.38  tff(c_70, plain, (r2_hidden('#skF_13', k7_relset_1('#skF_9', '#skF_10', '#skF_12', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.91/3.38  tff(c_1166, plain, (r2_hidden('#skF_13', k9_relat_1('#skF_12', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_1161, c_70])).
% 9.91/3.38  tff(c_2684, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2513, c_1166])).
% 9.91/3.38  tff(c_2686, plain, (![B_378]: (~v1_xboole_0(B_378) | ~r1_tarski('#skF_10', B_378))), inference(splitRight, [status(thm)], [c_2482])).
% 9.91/3.38  tff(c_2696, plain, (~v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_108, c_2686])).
% 9.91/3.38  tff(c_74, plain, (v1_funct_2('#skF_12', '#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.91/3.38  tff(c_170, plain, (![A_97, B_98, C_99]: (k1_relset_1(A_97, B_98, C_99)=k1_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.91/3.38  tff(c_184, plain, (k1_relset_1('#skF_9', '#skF_10', '#skF_12')=k1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_72, c_170])).
% 9.91/3.38  tff(c_4169, plain, (![B_439, A_440, C_441]: (k1_xboole_0=B_439 | k1_relset_1(A_440, B_439, C_441)=A_440 | ~v1_funct_2(C_441, A_440, B_439) | ~m1_subset_1(C_441, k1_zfmisc_1(k2_zfmisc_1(A_440, B_439))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 9.91/3.38  tff(c_4184, plain, (k1_xboole_0='#skF_10' | k1_relset_1('#skF_9', '#skF_10', '#skF_12')='#skF_9' | ~v1_funct_2('#skF_12', '#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_72, c_4169])).
% 9.91/3.38  tff(c_4190, plain, (k1_xboole_0='#skF_10' | k1_relat_1('#skF_12')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_184, c_4184])).
% 9.91/3.38  tff(c_4191, plain, (k1_relat_1('#skF_12')='#skF_9'), inference(splitLeft, [status(thm)], [c_4190])).
% 9.91/3.38  tff(c_36, plain, (![A_32, B_33, C_34]: (r2_hidden('#skF_6'(A_32, B_33, C_34), k1_relat_1(C_34)) | ~r2_hidden(A_32, k9_relat_1(C_34, B_33)) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.91/3.38  tff(c_4268, plain, (![A_32, B_33]: (r2_hidden('#skF_6'(A_32, B_33, '#skF_12'), '#skF_9') | ~r2_hidden(A_32, k9_relat_1('#skF_12', B_33)) | ~v1_relat_1('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_4191, c_36])).
% 9.91/3.38  tff(c_4850, plain, (![A_460, B_461]: (r2_hidden('#skF_6'(A_460, B_461, '#skF_12'), '#skF_9') | ~r2_hidden(A_460, k9_relat_1('#skF_12', B_461)))), inference(demodulation, [status(thm), theory('equality')], [c_119, c_4268])).
% 9.91/3.38  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.91/3.38  tff(c_5351, plain, (![A_483, B_484]: (m1_subset_1('#skF_6'(A_483, B_484, '#skF_12'), '#skF_9') | ~r2_hidden(A_483, k9_relat_1('#skF_12', B_484)))), inference(resolution, [status(thm)], [c_4850, c_10])).
% 9.91/3.38  tff(c_5396, plain, (m1_subset_1('#skF_6'('#skF_13', '#skF_11', '#skF_12'), '#skF_9')), inference(resolution, [status(thm)], [c_1166, c_5351])).
% 9.91/3.38  tff(c_76, plain, (v1_funct_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.91/3.38  tff(c_1457, plain, (![A_272, B_273, C_274]: (r2_hidden(k4_tarski('#skF_6'(A_272, B_273, C_274), A_272), C_274) | ~r2_hidden(A_272, k9_relat_1(C_274, B_273)) | ~v1_relat_1(C_274))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.91/3.38  tff(c_40, plain, (![C_40, A_38, B_39]: (k1_funct_1(C_40, A_38)=B_39 | ~r2_hidden(k4_tarski(A_38, B_39), C_40) | ~v1_funct_1(C_40) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.91/3.38  tff(c_13641, plain, (![C_674, A_675, B_676]: (k1_funct_1(C_674, '#skF_6'(A_675, B_676, C_674))=A_675 | ~v1_funct_1(C_674) | ~r2_hidden(A_675, k9_relat_1(C_674, B_676)) | ~v1_relat_1(C_674))), inference(resolution, [status(thm)], [c_1457, c_40])).
% 9.91/3.38  tff(c_13682, plain, (k1_funct_1('#skF_12', '#skF_6'('#skF_13', '#skF_11', '#skF_12'))='#skF_13' | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_1166, c_13641])).
% 9.91/3.38  tff(c_13712, plain, (k1_funct_1('#skF_12', '#skF_6'('#skF_13', '#skF_11', '#skF_12'))='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_76, c_13682])).
% 9.91/3.38  tff(c_609, plain, (![A_175, B_176, C_177]: (r2_hidden('#skF_6'(A_175, B_176, C_177), B_176) | ~r2_hidden(A_175, k9_relat_1(C_177, B_176)) | ~v1_relat_1(C_177))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.91/3.38  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.91/3.38  tff(c_15253, plain, (![A_692, B_693, C_694, B_695]: (r2_hidden('#skF_6'(A_692, B_693, C_694), B_695) | ~r1_tarski(B_693, B_695) | ~r2_hidden(A_692, k9_relat_1(C_694, B_693)) | ~v1_relat_1(C_694))), inference(resolution, [status(thm)], [c_609, c_2])).
% 9.91/3.38  tff(c_68, plain, (![F_64]: (k1_funct_1('#skF_12', F_64)!='#skF_13' | ~r2_hidden(F_64, '#skF_11') | ~m1_subset_1(F_64, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.91/3.38  tff(c_15558, plain, (![A_699, B_700, C_701]: (k1_funct_1('#skF_12', '#skF_6'(A_699, B_700, C_701))!='#skF_13' | ~m1_subset_1('#skF_6'(A_699, B_700, C_701), '#skF_9') | ~r1_tarski(B_700, '#skF_11') | ~r2_hidden(A_699, k9_relat_1(C_701, B_700)) | ~v1_relat_1(C_701))), inference(resolution, [status(thm)], [c_15253, c_68])).
% 9.91/3.38  tff(c_15624, plain, (k1_funct_1('#skF_12', '#skF_6'('#skF_13', '#skF_11', '#skF_12'))!='#skF_13' | ~m1_subset_1('#skF_6'('#skF_13', '#skF_11', '#skF_12'), '#skF_9') | ~r1_tarski('#skF_11', '#skF_11') | ~v1_relat_1('#skF_12')), inference(resolution, [status(thm)], [c_1166, c_15558])).
% 9.91/3.38  tff(c_15664, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_108, c_5396, c_13712, c_15624])).
% 9.91/3.38  tff(c_15665, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_4190])).
% 9.91/3.38  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.91/3.38  tff(c_15674, plain, (v1_xboole_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_15665, c_8])).
% 9.91/3.38  tff(c_15676, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2696, c_15674])).
% 9.91/3.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.91/3.38  
% 9.91/3.38  Inference rules
% 9.91/3.38  ----------------------
% 9.91/3.38  #Ref     : 0
% 9.91/3.38  #Sup     : 3444
% 9.91/3.38  #Fact    : 0
% 9.91/3.38  #Define  : 0
% 9.91/3.38  #Split   : 38
% 9.91/3.38  #Chain   : 0
% 9.91/3.38  #Close   : 0
% 9.91/3.38  
% 9.91/3.38  Ordering : KBO
% 9.91/3.38  
% 9.91/3.38  Simplification rules
% 9.91/3.38  ----------------------
% 9.91/3.38  #Subsume      : 1008
% 9.91/3.38  #Demod        : 1965
% 9.91/3.38  #Tautology    : 589
% 9.91/3.38  #SimpNegUnit  : 31
% 9.91/3.38  #BackRed      : 90
% 9.91/3.38  
% 9.91/3.38  #Partial instantiations: 0
% 9.91/3.38  #Strategies tried      : 1
% 9.91/3.38  
% 9.91/3.38  Timing (in seconds)
% 9.91/3.38  ----------------------
% 9.91/3.38  Preprocessing        : 0.36
% 9.91/3.38  Parsing              : 0.18
% 9.91/3.38  CNF conversion       : 0.03
% 9.91/3.38  Main loop            : 2.24
% 9.91/3.38  Inferencing          : 0.65
% 9.91/3.38  Reduction            : 0.62
% 9.91/3.38  Demodulation         : 0.44
% 9.91/3.38  BG Simplification    : 0.07
% 9.91/3.38  Subsumption          : 0.69
% 9.91/3.38  Abstraction          : 0.10
% 9.91/3.38  MUC search           : 0.00
% 9.91/3.38  Cooper               : 0.00
% 9.91/3.38  Total                : 2.64
% 9.91/3.38  Index Insertion      : 0.00
% 9.91/3.38  Index Deletion       : 0.00
% 9.91/3.38  Index Matching       : 0.00
% 9.91/3.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
