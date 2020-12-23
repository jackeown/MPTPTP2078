%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:09 EST 2020

% Result     : Theorem 7.93s
% Output     : CNFRefutation 8.29s
% Verified   : 
% Statistics : Number of formulae       :  259 (1993 expanded)
%              Number of leaves         :   48 ( 651 expanded)
%              Depth                    :   15
%              Number of atoms          :  460 (6018 expanded)
%              Number of equality atoms :  177 (1904 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_175,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_137,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_155,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_69,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_111,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_115,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

tff(c_40,plain,(
    ! [A_24,B_25] : v1_relat_1(k2_zfmisc_1(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_80,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_9082,plain,(
    ! [B_1207,A_1208] :
      ( v1_relat_1(B_1207)
      | ~ m1_subset_1(B_1207,k1_zfmisc_1(A_1208))
      | ~ v1_relat_1(A_1208) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_9085,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_9082])).

tff(c_9088,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_9085])).

tff(c_9147,plain,(
    ! [C_1220,A_1221,B_1222] :
      ( v4_relat_1(C_1220,A_1221)
      | ~ m1_subset_1(C_1220,k1_zfmisc_1(k2_zfmisc_1(A_1221,B_1222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_9157,plain,(
    v4_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_9147])).

tff(c_38,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_relat_1(B_23),A_22)
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_9352,plain,(
    ! [A_1260,B_1261,C_1262] :
      ( k2_relset_1(A_1260,B_1261,C_1262) = k2_relat_1(C_1262)
      | ~ m1_subset_1(C_1262,k1_zfmisc_1(k2_zfmisc_1(A_1260,B_1261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_9362,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_9352])).

tff(c_78,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_9364,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9362,c_78])).

tff(c_9409,plain,(
    ! [C_1273,A_1274,B_1275] :
      ( m1_subset_1(C_1273,k1_zfmisc_1(k2_zfmisc_1(A_1274,B_1275)))
      | ~ r1_tarski(k2_relat_1(C_1273),B_1275)
      | ~ r1_tarski(k1_relat_1(C_1273),A_1274)
      | ~ v1_relat_1(C_1273) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_76,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_93,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_82,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_20,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_156,plain,(
    ! [B_58,A_59] :
      ( v1_relat_1(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_159,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_156])).

tff(c_162,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_159])).

tff(c_1377,plain,(
    ! [A_255,B_256,C_257] :
      ( k1_relset_1(A_255,B_256,C_257) = k1_relat_1(C_257)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1387,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_1377])).

tff(c_1755,plain,(
    ! [B_317,A_318,C_319] :
      ( k1_xboole_0 = B_317
      | k1_relset_1(A_318,B_317,C_319) = A_318
      | ~ v1_funct_2(C_319,A_318,B_317)
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(A_318,B_317))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1761,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_1755])).

tff(c_1771,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1387,c_1761])).

tff(c_1772,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_1771])).

tff(c_1474,plain,(
    ! [A_273,B_274,C_275] :
      ( k2_relset_1(A_273,B_274,C_275) = k2_relat_1(C_275)
      | ~ m1_subset_1(C_275,k1_zfmisc_1(k2_zfmisc_1(A_273,B_274))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1484,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_1474])).

tff(c_1486,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1484,c_78])).

tff(c_1535,plain,(
    ! [C_286,A_287,B_288] :
      ( m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(A_287,B_288)))
      | ~ r1_tarski(k2_relat_1(C_286),B_288)
      | ~ r1_tarski(k1_relat_1(C_286),A_287)
      | ~ v1_relat_1(C_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_56,plain,(
    ! [A_35,B_36,C_37] :
      ( k1_relset_1(A_35,B_36,C_37) = k1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2523,plain,(
    ! [A_401,B_402,C_403] :
      ( k1_relset_1(A_401,B_402,C_403) = k1_relat_1(C_403)
      | ~ r1_tarski(k2_relat_1(C_403),B_402)
      | ~ r1_tarski(k1_relat_1(C_403),A_401)
      | ~ v1_relat_1(C_403) ) ),
    inference(resolution,[status(thm)],[c_1535,c_56])).

tff(c_2525,plain,(
    ! [A_401] :
      ( k1_relset_1(A_401,'#skF_5','#skF_6') = k1_relat_1('#skF_6')
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_401)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1486,c_2523])).

tff(c_2552,plain,(
    ! [A_406] :
      ( k1_relset_1(A_406,'#skF_5','#skF_6') = '#skF_3'
      | ~ r1_tarski('#skF_3',A_406) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_1772,c_1772,c_2525])).

tff(c_2557,plain,(
    k1_relset_1('#skF_3','#skF_5','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20,c_2552])).

tff(c_60,plain,(
    ! [C_43,A_41,B_42] :
      ( m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ r1_tarski(k2_relat_1(C_43),B_42)
      | ~ r1_tarski(k1_relat_1(C_43),A_41)
      | ~ v1_relat_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1697,plain,(
    ! [B_306,C_307,A_308] :
      ( k1_xboole_0 = B_306
      | v1_funct_2(C_307,A_308,B_306)
      | k1_relset_1(A_308,B_306,C_307) != A_308
      | ~ m1_subset_1(C_307,k1_zfmisc_1(k2_zfmisc_1(A_308,B_306))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_3094,plain,(
    ! [B_436,C_437,A_438] :
      ( k1_xboole_0 = B_436
      | v1_funct_2(C_437,A_438,B_436)
      | k1_relset_1(A_438,B_436,C_437) != A_438
      | ~ r1_tarski(k2_relat_1(C_437),B_436)
      | ~ r1_tarski(k1_relat_1(C_437),A_438)
      | ~ v1_relat_1(C_437) ) ),
    inference(resolution,[status(thm)],[c_60,c_1697])).

tff(c_3096,plain,(
    ! [A_438] :
      ( k1_xboole_0 = '#skF_5'
      | v1_funct_2('#skF_6',A_438,'#skF_5')
      | k1_relset_1(A_438,'#skF_5','#skF_6') != A_438
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_438)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1486,c_3094])).

tff(c_3108,plain,(
    ! [A_438] :
      ( k1_xboole_0 = '#skF_5'
      | v1_funct_2('#skF_6',A_438,'#skF_5')
      | k1_relset_1(A_438,'#skF_5','#skF_6') != A_438
      | ~ r1_tarski('#skF_3',A_438) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_1772,c_3096])).

tff(c_3159,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3108])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_522,plain,(
    ! [A_131,B_132,C_133] :
      ( ~ r1_xboole_0(A_131,B_132)
      | ~ r2_hidden(C_133,B_132)
      | ~ r2_hidden(C_133,A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_526,plain,(
    ! [C_134] : ~ r2_hidden(C_134,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_522])).

tff(c_539,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_526])).

tff(c_3230,plain,(
    ! [B_2] : r1_tarski('#skF_5',B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3159,c_539])).

tff(c_440,plain,(
    ! [B_115,A_116] :
      ( B_115 = A_116
      | ~ r1_tarski(B_115,A_116)
      | ~ r1_tarski(A_116,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_448,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_relset_1('#skF_3','#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_78,c_440])).

tff(c_581,plain,(
    ~ r1_tarski('#skF_5',k2_relset_1('#skF_3','#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_448])).

tff(c_1485,plain,(
    ~ r1_tarski('#skF_5',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1484,c_581])).

tff(c_3262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3230,c_1485])).

tff(c_3265,plain,(
    ! [A_450] :
      ( v1_funct_2('#skF_6',A_450,'#skF_5')
      | k1_relset_1(A_450,'#skF_5','#skF_6') != A_450
      | ~ r1_tarski('#skF_3',A_450) ) ),
    inference(splitRight,[status(thm)],[c_3108])).

tff(c_84,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_86,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_74])).

tff(c_155,plain,(
    ~ v1_funct_2('#skF_6','#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_3271,plain,
    ( k1_relset_1('#skF_3','#skF_5','#skF_6') != '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_3265,c_155])).

tff(c_3276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2557,c_3271])).

tff(c_3277,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_448])).

tff(c_4108,plain,(
    ! [A_567,B_568,C_569] :
      ( k2_relset_1(A_567,B_568,C_569) = k2_relat_1(C_569)
      | ~ m1_subset_1(C_569,k1_zfmisc_1(k2_zfmisc_1(A_567,B_568))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_4111,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_4108])).

tff(c_4119,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3277,c_4111])).

tff(c_173,plain,(
    ! [A_64] :
      ( k1_relat_1(A_64) = k1_xboole_0
      | k2_relat_1(A_64) != k1_xboole_0
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_183,plain,
    ( k1_relat_1('#skF_6') = k1_xboole_0
    | k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_162,c_173])).

tff(c_186,plain,(
    k2_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_4120,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4119,c_186])).

tff(c_4142,plain,(
    ! [A_575,B_576,C_577] :
      ( k1_relset_1(A_575,B_576,C_577) = k1_relat_1(C_577)
      | ~ m1_subset_1(C_577,k1_zfmisc_1(k2_zfmisc_1(A_575,B_576))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_4152,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_4142])).

tff(c_4447,plain,(
    ! [B_625,A_626,C_627] :
      ( k1_xboole_0 = B_625
      | k1_relset_1(A_626,B_625,C_627) = A_626
      | ~ v1_funct_2(C_627,A_626,B_625)
      | ~ m1_subset_1(C_627,k1_zfmisc_1(k2_zfmisc_1(A_626,B_625))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_4453,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_4447])).

tff(c_4463,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4152,c_4453])).

tff(c_4464,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_4463])).

tff(c_4177,plain,(
    ! [C_581,A_582,B_583] :
      ( m1_subset_1(C_581,k1_zfmisc_1(k2_zfmisc_1(A_582,B_583)))
      | ~ r1_tarski(k2_relat_1(C_581),B_583)
      | ~ r1_tarski(k1_relat_1(C_581),A_582)
      | ~ v1_relat_1(C_581) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_5339,plain,(
    ! [A_732,B_733,C_734] :
      ( k1_relset_1(A_732,B_733,C_734) = k1_relat_1(C_734)
      | ~ r1_tarski(k2_relat_1(C_734),B_733)
      | ~ r1_tarski(k1_relat_1(C_734),A_732)
      | ~ v1_relat_1(C_734) ) ),
    inference(resolution,[status(thm)],[c_4177,c_56])).

tff(c_5343,plain,(
    ! [A_732,B_733] :
      ( k1_relset_1(A_732,B_733,'#skF_6') = k1_relat_1('#skF_6')
      | ~ r1_tarski('#skF_5',B_733)
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_732)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4119,c_5339])).

tff(c_5367,plain,(
    ! [A_737,B_738] :
      ( k1_relset_1(A_737,B_738,'#skF_6') = '#skF_3'
      | ~ r1_tarski('#skF_5',B_738)
      | ~ r1_tarski('#skF_3',A_737) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_4464,c_4464,c_5343])).

tff(c_5372,plain,(
    ! [A_739] :
      ( k1_relset_1(A_739,'#skF_5','#skF_6') = '#skF_3'
      | ~ r1_tarski('#skF_3',A_739) ) ),
    inference(resolution,[status(thm)],[c_20,c_5367])).

tff(c_5377,plain,(
    k1_relset_1('#skF_3','#skF_5','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20,c_5372])).

tff(c_4308,plain,(
    ! [B_602,C_603,A_604] :
      ( k1_xboole_0 = B_602
      | v1_funct_2(C_603,A_604,B_602)
      | k1_relset_1(A_604,B_602,C_603) != A_604
      | ~ m1_subset_1(C_603,k1_zfmisc_1(k2_zfmisc_1(A_604,B_602))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_5970,plain,(
    ! [B_792,C_793,A_794] :
      ( k1_xboole_0 = B_792
      | v1_funct_2(C_793,A_794,B_792)
      | k1_relset_1(A_794,B_792,C_793) != A_794
      | ~ r1_tarski(k2_relat_1(C_793),B_792)
      | ~ r1_tarski(k1_relat_1(C_793),A_794)
      | ~ v1_relat_1(C_793) ) ),
    inference(resolution,[status(thm)],[c_60,c_4308])).

tff(c_5974,plain,(
    ! [B_792,A_794] :
      ( k1_xboole_0 = B_792
      | v1_funct_2('#skF_6',A_794,B_792)
      | k1_relset_1(A_794,B_792,'#skF_6') != A_794
      | ~ r1_tarski('#skF_5',B_792)
      | ~ r1_tarski(k1_relat_1('#skF_6'),A_794)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4119,c_5970])).

tff(c_6034,plain,(
    ! [B_803,A_804] :
      ( k1_xboole_0 = B_803
      | v1_funct_2('#skF_6',A_804,B_803)
      | k1_relset_1(A_804,B_803,'#skF_6') != A_804
      | ~ r1_tarski('#skF_5',B_803)
      | ~ r1_tarski('#skF_3',A_804) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_4464,c_5974])).

tff(c_6043,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_3','#skF_5','#skF_6') != '#skF_3'
    | ~ r1_tarski('#skF_5','#skF_5')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_6034,c_155])).

tff(c_6048,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_5377,c_6043])).

tff(c_6050,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4120,c_6048])).

tff(c_6051,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_6579,plain,(
    ! [A_903,B_904,C_905] :
      ( k1_relset_1(A_903,B_904,C_905) = k1_relat_1(C_905)
      | ~ m1_subset_1(C_905,k1_zfmisc_1(k2_zfmisc_1(A_903,B_904))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_6582,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_6579])).

tff(c_6590,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6051,c_6582])).

tff(c_6818,plain,(
    ! [B_946,A_947,C_948] :
      ( k1_xboole_0 = B_946
      | k1_relset_1(A_947,B_946,C_948) = A_947
      | ~ v1_funct_2(C_948,A_947,B_946)
      | ~ m1_subset_1(C_948,k1_zfmisc_1(k2_zfmisc_1(A_947,B_946))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_6824,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_6818])).

tff(c_6834,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_6590,c_6824])).

tff(c_6835,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_6834])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6884,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6835,c_8])).

tff(c_30,plain,(
    ! [B_15] : k2_zfmisc_1(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6881,plain,(
    ! [B_15] : k2_zfmisc_1('#skF_3',B_15) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6835,c_6835,c_30])).

tff(c_6462,plain,(
    ! [C_881,B_882,A_883] :
      ( ~ v1_xboole_0(C_881)
      | ~ m1_subset_1(B_882,k1_zfmisc_1(C_881))
      | ~ r2_hidden(A_883,B_882) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6465,plain,(
    ! [A_883] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'))
      | ~ r2_hidden(A_883,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_80,c_6462])).

tff(c_6466,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6465])).

tff(c_7047,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6881,c_6466])).

tff(c_7051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6884,c_7047])).

tff(c_7054,plain,(
    ! [A_959] : ~ r2_hidden(A_959,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_6465])).

tff(c_7070,plain,(
    ! [B_960] : r1_xboole_0('#skF_6',B_960) ),
    inference(resolution,[status(thm)],[c_14,c_7054])).

tff(c_24,plain,(
    ! [A_13] :
      ( ~ r1_xboole_0(A_13,A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_7078,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7070,c_24])).

tff(c_7123,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7078,c_93])).

tff(c_7113,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7078,c_6051])).

tff(c_8136,plain,(
    ! [A_1081,B_1082,C_1083] :
      ( k1_relset_1(A_1081,B_1082,C_1083) = k1_relat_1(C_1083)
      | ~ m1_subset_1(C_1083,k1_zfmisc_1(k2_zfmisc_1(A_1081,B_1082))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_8145,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_8136])).

tff(c_8147,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7113,c_8145])).

tff(c_72,plain,(
    ! [B_45,A_44,C_46] :
      ( k1_xboole_0 = B_45
      | k1_relset_1(A_44,B_45,C_46) = A_44
      | ~ v1_funct_2(C_46,A_44,B_45)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_8505,plain,(
    ! [B_1133,A_1134,C_1135] :
      ( B_1133 = '#skF_6'
      | k1_relset_1(A_1134,B_1133,C_1135) = A_1134
      | ~ v1_funct_2(C_1135,A_1134,B_1133)
      | ~ m1_subset_1(C_1135,k1_zfmisc_1(k2_zfmisc_1(A_1134,B_1133))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7078,c_72])).

tff(c_8517,plain,
    ( '#skF_6' = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_8505])).

tff(c_8522,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_8147,c_8517])).

tff(c_8523,plain,(
    '#skF_6' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_7123,c_8522])).

tff(c_7313,plain,(
    ! [A_978,B_979,C_980] :
      ( k1_relset_1(A_978,B_979,C_980) = k1_relat_1(C_980)
      | ~ m1_subset_1(C_980,k1_zfmisc_1(k2_zfmisc_1(A_978,B_979))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_7322,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_7313])).

tff(c_7324,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7113,c_7322])).

tff(c_7810,plain,(
    ! [B_1063,A_1064,C_1065] :
      ( B_1063 = '#skF_6'
      | k1_relset_1(A_1064,B_1063,C_1065) = A_1064
      | ~ v1_funct_2(C_1065,A_1064,B_1063)
      | ~ m1_subset_1(C_1065,k1_zfmisc_1(k2_zfmisc_1(A_1064,B_1063))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7078,c_72])).

tff(c_7822,plain,
    ( '#skF_6' = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_7810])).

tff(c_7827,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_7324,c_7822])).

tff(c_7828,plain,(
    '#skF_6' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_7123,c_7827])).

tff(c_7121,plain,(
    ! [B_15] : k2_zfmisc_1('#skF_6',B_15) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7078,c_7078,c_30])).

tff(c_7870,plain,(
    ! [B_15] : k2_zfmisc_1('#skF_3',B_15) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7828,c_7828,c_7121])).

tff(c_7884,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7828,c_80])).

tff(c_8038,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7870,c_7884])).

tff(c_28,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_62,plain,(
    ! [A_44] :
      ( v1_funct_2(k1_xboole_0,A_44,k1_xboole_0)
      | k1_xboole_0 = A_44
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_44,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_90,plain,(
    ! [A_44] :
      ( v1_funct_2(k1_xboole_0,A_44,k1_xboole_0)
      | k1_xboole_0 = A_44
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_62])).

tff(c_7219,plain,(
    ! [A_44] :
      ( v1_funct_2('#skF_6',A_44,'#skF_6')
      | A_44 = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7078,c_7078,c_7078,c_7078,c_7078,c_90])).

tff(c_7220,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_7219])).

tff(c_7868,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7828,c_7828,c_7220])).

tff(c_8133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8038,c_7868])).

tff(c_8135,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_7219])).

tff(c_8448,plain,(
    ! [B_1124,C_1125] :
      ( k1_relset_1('#skF_6',B_1124,C_1125) = k1_relat_1(C_1125)
      | ~ m1_subset_1(C_1125,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7121,c_8136])).

tff(c_8450,plain,(
    ! [B_1124] : k1_relset_1('#skF_6',B_1124,'#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8135,c_8448])).

tff(c_8452,plain,(
    ! [B_1124] : k1_relset_1('#skF_6',B_1124,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7113,c_8450])).

tff(c_66,plain,(
    ! [C_46,B_45] :
      ( v1_funct_2(C_46,k1_xboole_0,B_45)
      | k1_relset_1(k1_xboole_0,B_45,C_46) != k1_xboole_0
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_88,plain,(
    ! [C_46,B_45] :
      ( v1_funct_2(C_46,k1_xboole_0,B_45)
      | k1_relset_1(k1_xboole_0,B_45,C_46) != k1_xboole_0
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_66])).

tff(c_8389,plain,(
    ! [C_1113,B_1114] :
      ( v1_funct_2(C_1113,'#skF_6',B_1114)
      | k1_relset_1('#skF_6',B_1114,C_1113) != '#skF_6'
      | ~ m1_subset_1(C_1113,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7078,c_7078,c_7078,c_7078,c_88])).

tff(c_8392,plain,(
    ! [B_1114] :
      ( v1_funct_2('#skF_6','#skF_6',B_1114)
      | k1_relset_1('#skF_6',B_1114,'#skF_6') != '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_8135,c_8389])).

tff(c_8454,plain,(
    ! [B_1114] : v1_funct_2('#skF_6','#skF_6',B_1114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8452,c_8392])).

tff(c_8528,plain,(
    ! [B_1114] : v1_funct_2('#skF_3','#skF_3',B_1114) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8523,c_8523,c_8454])).

tff(c_8569,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8523,c_155])).

tff(c_8816,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8528,c_8569])).

tff(c_8817,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_9429,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_9409,c_8817])).

tff(c_9446,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9088,c_9364,c_9429])).

tff(c_9449,plain,
    ( ~ v4_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_9446])).

tff(c_9453,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9088,c_9157,c_9449])).

tff(c_9455,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_9477,plain,(
    ! [A_1278] : k2_zfmisc_1(A_1278,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9455,c_9455,c_28])).

tff(c_9481,plain,(
    v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_9477,c_40])).

tff(c_46,plain,(
    ! [A_29] :
      ( k1_relat_1(A_29) = k1_xboole_0
      | k2_relat_1(A_29) != k1_xboole_0
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_9558,plain,(
    ! [A_1292] :
      ( k1_relat_1(A_1292) = '#skF_4'
      | k2_relat_1(A_1292) != '#skF_4'
      | ~ v1_relat_1(A_1292) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9455,c_9455,c_46])).

tff(c_9565,plain,
    ( k1_relat_1('#skF_4') = '#skF_4'
    | k2_relat_1('#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_9481,c_9558])).

tff(c_9567,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_9565])).

tff(c_50,plain,(
    ! [B_31,A_30] :
      ( r1_tarski(k7_relat_1(B_31,A_30),B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_9454,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_9462,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9455,c_9454])).

tff(c_9457,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9454,c_8])).

tff(c_9467,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9462,c_9457])).

tff(c_9476,plain,(
    ! [A_14] : k2_zfmisc_1(A_14,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9455,c_9455,c_28])).

tff(c_9512,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9476,c_9462,c_80])).

tff(c_9648,plain,(
    ! [C_1310,B_1311,A_1312] :
      ( ~ v1_xboole_0(C_1310)
      | ~ m1_subset_1(B_1311,k1_zfmisc_1(C_1310))
      | ~ r2_hidden(A_1312,B_1311) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_9650,plain,(
    ! [A_1312] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_1312,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_9512,c_9648])).

tff(c_9654,plain,(
    ! [A_1313] : ~ r2_hidden(A_1313,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9467,c_9650])).

tff(c_9684,plain,(
    ! [B_1318] : r1_xboole_0('#skF_6',B_1318) ),
    inference(resolution,[status(thm)],[c_14,c_9654])).

tff(c_9505,plain,(
    ! [A_13] :
      ( ~ r1_xboole_0(A_13,A_13)
      | A_13 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9455,c_24])).

tff(c_9689,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9684,c_9505])).

tff(c_9670,plain,(
    ! [B_1314] : r1_tarski('#skF_6',B_1314) ),
    inference(resolution,[status(thm)],[c_6,c_9654])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( B_12 = A_11
      | ~ r1_tarski(B_12,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_9673,plain,(
    ! [B_1314] :
      ( B_1314 = '#skF_6'
      | ~ r1_tarski(B_1314,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_9670,c_16])).

tff(c_9772,plain,(
    ! [B_1326] :
      ( B_1326 = '#skF_4'
      | ~ r1_tarski(B_1326,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9689,c_9689,c_9673])).

tff(c_9784,plain,(
    ! [A_30] :
      ( k7_relat_1('#skF_4',A_30) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_9772])).

tff(c_9797,plain,(
    ! [A_1327] : k7_relat_1('#skF_4',A_1327) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9481,c_9784])).

tff(c_42,plain,(
    ! [B_27,A_26] :
      ( k2_relat_1(k7_relat_1(B_27,A_26)) = k9_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_9802,plain,(
    ! [A_1327] :
      ( k9_relat_1('#skF_4',A_1327) = k2_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9797,c_42])).

tff(c_9814,plain,(
    ! [A_1328] : k9_relat_1('#skF_4',A_1328) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9481,c_9802])).

tff(c_44,plain,(
    ! [A_28] :
      ( k9_relat_1(A_28,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_9514,plain,(
    ! [A_1281] :
      ( k9_relat_1(A_1281,'#skF_4') = '#skF_4'
      | ~ v1_relat_1(A_1281) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9455,c_9455,c_44])).

tff(c_9521,plain,(
    k9_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9481,c_9514])).

tff(c_9818,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_9814,c_9521])).

tff(c_9825,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9567,c_9818])).

tff(c_9826,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9565])).

tff(c_10279,plain,(
    ! [C_1403,B_1404,A_1405] :
      ( ~ v1_xboole_0(C_1403)
      | ~ m1_subset_1(B_1404,k1_zfmisc_1(C_1403))
      | ~ r2_hidden(A_1405,B_1404) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10281,plain,(
    ! [A_1405] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_1405,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_9512,c_10279])).

tff(c_10285,plain,(
    ! [A_1406] : ~ r2_hidden(A_1406,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9467,c_10281])).

tff(c_10301,plain,(
    ! [B_1407] : r1_tarski('#skF_6',B_1407) ),
    inference(resolution,[status(thm)],[c_6,c_10285])).

tff(c_9456,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9454,c_9454,c_22])).

tff(c_9473,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9462,c_9462,c_9456])).

tff(c_10178,plain,(
    ! [A_1389,B_1390,C_1391] :
      ( ~ r1_xboole_0(A_1389,B_1390)
      | ~ r2_hidden(C_1391,B_1390)
      | ~ r2_hidden(C_1391,A_1389) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10182,plain,(
    ! [C_1392] : ~ r2_hidden(C_1392,'#skF_4') ),
    inference(resolution,[status(thm)],[c_9473,c_10178])).

tff(c_10200,plain,(
    ! [B_1393] : r1_tarski('#skF_4',B_1393) ),
    inference(resolution,[status(thm)],[c_6,c_10182])).

tff(c_10203,plain,(
    ! [B_1393] :
      ( B_1393 = '#skF_4'
      | ~ r1_tarski(B_1393,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10200,c_16])).

tff(c_10308,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10301,c_10203])).

tff(c_10319,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10308,c_9512])).

tff(c_9486,plain,(
    ! [B_15] : k2_zfmisc_1('#skF_4',B_15) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9455,c_9455,c_30])).

tff(c_10533,plain,(
    ! [A_1437,B_1438,C_1439] :
      ( k1_relset_1(A_1437,B_1438,C_1439) = k1_relat_1(C_1439)
      | ~ m1_subset_1(C_1439,k1_zfmisc_1(k2_zfmisc_1(A_1437,B_1438))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_10547,plain,(
    ! [B_1442,C_1443] :
      ( k1_relset_1('#skF_4',B_1442,C_1443) = k1_relat_1(C_1443)
      | ~ m1_subset_1(C_1443,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9486,c_10533])).

tff(c_10549,plain,(
    ! [B_1442] : k1_relset_1('#skF_4',B_1442,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10319,c_10547])).

tff(c_10551,plain,(
    ! [B_1442] : k1_relset_1('#skF_4',B_1442,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9826,c_10549])).

tff(c_10871,plain,(
    ! [C_1492,B_1493] :
      ( v1_funct_2(C_1492,'#skF_4',B_1493)
      | k1_relset_1('#skF_4',B_1493,C_1492) != '#skF_4'
      | ~ m1_subset_1(C_1492,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9455,c_9455,c_9455,c_9455,c_88])).

tff(c_10873,plain,(
    ! [B_1493] :
      ( v1_funct_2('#skF_4','#skF_4',B_1493)
      | k1_relset_1('#skF_4',B_1493,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_10319,c_10871])).

tff(c_10876,plain,(
    ! [B_1493] : v1_funct_2('#skF_4','#skF_4',B_1493) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10551,c_10873])).

tff(c_9542,plain,(
    ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9462,c_9512,c_9486,c_9462,c_86])).

tff(c_10318,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10308,c_9542])).

tff(c_10880,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10876,c_10318])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 10:50:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.93/2.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.18/2.79  
% 8.18/2.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.18/2.79  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 8.18/2.79  
% 8.18/2.79  %Foreground sorts:
% 8.18/2.79  
% 8.18/2.79  
% 8.18/2.79  %Background operators:
% 8.18/2.79  
% 8.18/2.79  
% 8.18/2.79  %Foreground operators:
% 8.18/2.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.18/2.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.18/2.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.18/2.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.18/2.79  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.18/2.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.18/2.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.18/2.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.18/2.79  tff('#skF_5', type, '#skF_5': $i).
% 8.18/2.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.18/2.79  tff('#skF_6', type, '#skF_6': $i).
% 8.18/2.79  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.18/2.79  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.18/2.79  tff('#skF_3', type, '#skF_3': $i).
% 8.18/2.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.18/2.79  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.18/2.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.18/2.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.18/2.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.18/2.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.18/2.79  tff('#skF_4', type, '#skF_4': $i).
% 8.18/2.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.18/2.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.18/2.79  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.18/2.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.18/2.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.18/2.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.18/2.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.18/2.79  
% 8.29/2.82  tff(f_97, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.29/2.82  tff(f_175, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 8.29/2.82  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.29/2.82  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.29/2.82  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 8.29/2.82  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.29/2.82  tff(f_137, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 8.29/2.82  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 8.29/2.82  tff(f_57, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.29/2.82  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.29/2.82  tff(f_155, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.29/2.82  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.29/2.82  tff(f_69, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 8.29/2.82  tff(f_111, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 8.29/2.82  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.29/2.82  tff(f_75, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.29/2.82  tff(f_82, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 8.29/2.82  tff(f_115, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 8.29/2.82  tff(f_101, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 8.29/2.82  tff(f_105, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_relat_1)).
% 8.29/2.82  tff(c_40, plain, (![A_24, B_25]: (v1_relat_1(k2_zfmisc_1(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.29/2.82  tff(c_80, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.29/2.82  tff(c_9082, plain, (![B_1207, A_1208]: (v1_relat_1(B_1207) | ~m1_subset_1(B_1207, k1_zfmisc_1(A_1208)) | ~v1_relat_1(A_1208))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.29/2.82  tff(c_9085, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_9082])).
% 8.29/2.82  tff(c_9088, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_9085])).
% 8.29/2.82  tff(c_9147, plain, (![C_1220, A_1221, B_1222]: (v4_relat_1(C_1220, A_1221) | ~m1_subset_1(C_1220, k1_zfmisc_1(k2_zfmisc_1(A_1221, B_1222))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.29/2.82  tff(c_9157, plain, (v4_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_80, c_9147])).
% 8.29/2.82  tff(c_38, plain, (![B_23, A_22]: (r1_tarski(k1_relat_1(B_23), A_22) | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.29/2.82  tff(c_9352, plain, (![A_1260, B_1261, C_1262]: (k2_relset_1(A_1260, B_1261, C_1262)=k2_relat_1(C_1262) | ~m1_subset_1(C_1262, k1_zfmisc_1(k2_zfmisc_1(A_1260, B_1261))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.29/2.82  tff(c_9362, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_9352])).
% 8.29/2.82  tff(c_78, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.29/2.82  tff(c_9364, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9362, c_78])).
% 8.29/2.82  tff(c_9409, plain, (![C_1273, A_1274, B_1275]: (m1_subset_1(C_1273, k1_zfmisc_1(k2_zfmisc_1(A_1274, B_1275))) | ~r1_tarski(k2_relat_1(C_1273), B_1275) | ~r1_tarski(k1_relat_1(C_1273), A_1274) | ~v1_relat_1(C_1273))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.29/2.82  tff(c_14, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.29/2.82  tff(c_76, plain, (k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.29/2.82  tff(c_93, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_76])).
% 8.29/2.82  tff(c_82, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.29/2.82  tff(c_20, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.29/2.82  tff(c_156, plain, (![B_58, A_59]: (v1_relat_1(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.29/2.82  tff(c_159, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_80, c_156])).
% 8.29/2.82  tff(c_162, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_159])).
% 8.29/2.82  tff(c_1377, plain, (![A_255, B_256, C_257]: (k1_relset_1(A_255, B_256, C_257)=k1_relat_1(C_257) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.29/2.82  tff(c_1387, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_1377])).
% 8.29/2.82  tff(c_1755, plain, (![B_317, A_318, C_319]: (k1_xboole_0=B_317 | k1_relset_1(A_318, B_317, C_319)=A_318 | ~v1_funct_2(C_319, A_318, B_317) | ~m1_subset_1(C_319, k1_zfmisc_1(k2_zfmisc_1(A_318, B_317))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.29/2.82  tff(c_1761, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_1755])).
% 8.29/2.82  tff(c_1771, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1387, c_1761])).
% 8.29/2.82  tff(c_1772, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_93, c_1771])).
% 8.29/2.82  tff(c_1474, plain, (![A_273, B_274, C_275]: (k2_relset_1(A_273, B_274, C_275)=k2_relat_1(C_275) | ~m1_subset_1(C_275, k1_zfmisc_1(k2_zfmisc_1(A_273, B_274))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.29/2.82  tff(c_1484, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_1474])).
% 8.29/2.82  tff(c_1486, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1484, c_78])).
% 8.29/2.82  tff(c_1535, plain, (![C_286, A_287, B_288]: (m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))) | ~r1_tarski(k2_relat_1(C_286), B_288) | ~r1_tarski(k1_relat_1(C_286), A_287) | ~v1_relat_1(C_286))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.29/2.82  tff(c_56, plain, (![A_35, B_36, C_37]: (k1_relset_1(A_35, B_36, C_37)=k1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.29/2.82  tff(c_2523, plain, (![A_401, B_402, C_403]: (k1_relset_1(A_401, B_402, C_403)=k1_relat_1(C_403) | ~r1_tarski(k2_relat_1(C_403), B_402) | ~r1_tarski(k1_relat_1(C_403), A_401) | ~v1_relat_1(C_403))), inference(resolution, [status(thm)], [c_1535, c_56])).
% 8.29/2.82  tff(c_2525, plain, (![A_401]: (k1_relset_1(A_401, '#skF_5', '#skF_6')=k1_relat_1('#skF_6') | ~r1_tarski(k1_relat_1('#skF_6'), A_401) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1486, c_2523])).
% 8.29/2.82  tff(c_2552, plain, (![A_406]: (k1_relset_1(A_406, '#skF_5', '#skF_6')='#skF_3' | ~r1_tarski('#skF_3', A_406))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_1772, c_1772, c_2525])).
% 8.29/2.82  tff(c_2557, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_20, c_2552])).
% 8.29/2.82  tff(c_60, plain, (![C_43, A_41, B_42]: (m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~r1_tarski(k2_relat_1(C_43), B_42) | ~r1_tarski(k1_relat_1(C_43), A_41) | ~v1_relat_1(C_43))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.29/2.82  tff(c_1697, plain, (![B_306, C_307, A_308]: (k1_xboole_0=B_306 | v1_funct_2(C_307, A_308, B_306) | k1_relset_1(A_308, B_306, C_307)!=A_308 | ~m1_subset_1(C_307, k1_zfmisc_1(k2_zfmisc_1(A_308, B_306))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.29/2.82  tff(c_3094, plain, (![B_436, C_437, A_438]: (k1_xboole_0=B_436 | v1_funct_2(C_437, A_438, B_436) | k1_relset_1(A_438, B_436, C_437)!=A_438 | ~r1_tarski(k2_relat_1(C_437), B_436) | ~r1_tarski(k1_relat_1(C_437), A_438) | ~v1_relat_1(C_437))), inference(resolution, [status(thm)], [c_60, c_1697])).
% 8.29/2.82  tff(c_3096, plain, (![A_438]: (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', A_438, '#skF_5') | k1_relset_1(A_438, '#skF_5', '#skF_6')!=A_438 | ~r1_tarski(k1_relat_1('#skF_6'), A_438) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1486, c_3094])).
% 8.29/2.82  tff(c_3108, plain, (![A_438]: (k1_xboole_0='#skF_5' | v1_funct_2('#skF_6', A_438, '#skF_5') | k1_relset_1(A_438, '#skF_5', '#skF_6')!=A_438 | ~r1_tarski('#skF_3', A_438))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_1772, c_3096])).
% 8.29/2.82  tff(c_3159, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_3108])).
% 8.29/2.82  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.29/2.82  tff(c_22, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.29/2.82  tff(c_522, plain, (![A_131, B_132, C_133]: (~r1_xboole_0(A_131, B_132) | ~r2_hidden(C_133, B_132) | ~r2_hidden(C_133, A_131))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.29/2.82  tff(c_526, plain, (![C_134]: (~r2_hidden(C_134, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_522])).
% 8.29/2.82  tff(c_539, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_526])).
% 8.29/2.82  tff(c_3230, plain, (![B_2]: (r1_tarski('#skF_5', B_2))), inference(demodulation, [status(thm), theory('equality')], [c_3159, c_539])).
% 8.29/2.82  tff(c_440, plain, (![B_115, A_116]: (B_115=A_116 | ~r1_tarski(B_115, A_116) | ~r1_tarski(A_116, B_115))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.29/2.82  tff(c_448, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_5' | ~r1_tarski('#skF_5', k2_relset_1('#skF_3', '#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_78, c_440])).
% 8.29/2.82  tff(c_581, plain, (~r1_tarski('#skF_5', k2_relset_1('#skF_3', '#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_448])).
% 8.29/2.82  tff(c_1485, plain, (~r1_tarski('#skF_5', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1484, c_581])).
% 8.29/2.82  tff(c_3262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3230, c_1485])).
% 8.29/2.82  tff(c_3265, plain, (![A_450]: (v1_funct_2('#skF_6', A_450, '#skF_5') | k1_relset_1(A_450, '#skF_5', '#skF_6')!=A_450 | ~r1_tarski('#skF_3', A_450))), inference(splitRight, [status(thm)], [c_3108])).
% 8.29/2.82  tff(c_84, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.29/2.82  tff(c_74, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_5') | ~v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.29/2.82  tff(c_86, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_74])).
% 8.29/2.82  tff(c_155, plain, (~v1_funct_2('#skF_6', '#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_86])).
% 8.29/2.82  tff(c_3271, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')!='#skF_3' | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_3265, c_155])).
% 8.29/2.82  tff(c_3276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_2557, c_3271])).
% 8.29/2.82  tff(c_3277, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_448])).
% 8.29/2.82  tff(c_4108, plain, (![A_567, B_568, C_569]: (k2_relset_1(A_567, B_568, C_569)=k2_relat_1(C_569) | ~m1_subset_1(C_569, k1_zfmisc_1(k2_zfmisc_1(A_567, B_568))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.29/2.82  tff(c_4111, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_4108])).
% 8.29/2.82  tff(c_4119, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3277, c_4111])).
% 8.29/2.82  tff(c_173, plain, (![A_64]: (k1_relat_1(A_64)=k1_xboole_0 | k2_relat_1(A_64)!=k1_xboole_0 | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.29/2.82  tff(c_183, plain, (k1_relat_1('#skF_6')=k1_xboole_0 | k2_relat_1('#skF_6')!=k1_xboole_0), inference(resolution, [status(thm)], [c_162, c_173])).
% 8.29/2.82  tff(c_186, plain, (k2_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_183])).
% 8.29/2.82  tff(c_4120, plain, (k1_xboole_0!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4119, c_186])).
% 8.29/2.82  tff(c_4142, plain, (![A_575, B_576, C_577]: (k1_relset_1(A_575, B_576, C_577)=k1_relat_1(C_577) | ~m1_subset_1(C_577, k1_zfmisc_1(k2_zfmisc_1(A_575, B_576))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.29/2.82  tff(c_4152, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_4142])).
% 8.29/2.82  tff(c_4447, plain, (![B_625, A_626, C_627]: (k1_xboole_0=B_625 | k1_relset_1(A_626, B_625, C_627)=A_626 | ~v1_funct_2(C_627, A_626, B_625) | ~m1_subset_1(C_627, k1_zfmisc_1(k2_zfmisc_1(A_626, B_625))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.29/2.82  tff(c_4453, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_4447])).
% 8.29/2.82  tff(c_4463, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_4152, c_4453])).
% 8.29/2.82  tff(c_4464, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_93, c_4463])).
% 8.29/2.82  tff(c_4177, plain, (![C_581, A_582, B_583]: (m1_subset_1(C_581, k1_zfmisc_1(k2_zfmisc_1(A_582, B_583))) | ~r1_tarski(k2_relat_1(C_581), B_583) | ~r1_tarski(k1_relat_1(C_581), A_582) | ~v1_relat_1(C_581))), inference(cnfTransformation, [status(thm)], [f_137])).
% 8.29/2.82  tff(c_5339, plain, (![A_732, B_733, C_734]: (k1_relset_1(A_732, B_733, C_734)=k1_relat_1(C_734) | ~r1_tarski(k2_relat_1(C_734), B_733) | ~r1_tarski(k1_relat_1(C_734), A_732) | ~v1_relat_1(C_734))), inference(resolution, [status(thm)], [c_4177, c_56])).
% 8.29/2.82  tff(c_5343, plain, (![A_732, B_733]: (k1_relset_1(A_732, B_733, '#skF_6')=k1_relat_1('#skF_6') | ~r1_tarski('#skF_5', B_733) | ~r1_tarski(k1_relat_1('#skF_6'), A_732) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4119, c_5339])).
% 8.29/2.82  tff(c_5367, plain, (![A_737, B_738]: (k1_relset_1(A_737, B_738, '#skF_6')='#skF_3' | ~r1_tarski('#skF_5', B_738) | ~r1_tarski('#skF_3', A_737))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_4464, c_4464, c_5343])).
% 8.29/2.82  tff(c_5372, plain, (![A_739]: (k1_relset_1(A_739, '#skF_5', '#skF_6')='#skF_3' | ~r1_tarski('#skF_3', A_739))), inference(resolution, [status(thm)], [c_20, c_5367])).
% 8.29/2.82  tff(c_5377, plain, (k1_relset_1('#skF_3', '#skF_5', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_20, c_5372])).
% 8.29/2.82  tff(c_4308, plain, (![B_602, C_603, A_604]: (k1_xboole_0=B_602 | v1_funct_2(C_603, A_604, B_602) | k1_relset_1(A_604, B_602, C_603)!=A_604 | ~m1_subset_1(C_603, k1_zfmisc_1(k2_zfmisc_1(A_604, B_602))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.29/2.82  tff(c_5970, plain, (![B_792, C_793, A_794]: (k1_xboole_0=B_792 | v1_funct_2(C_793, A_794, B_792) | k1_relset_1(A_794, B_792, C_793)!=A_794 | ~r1_tarski(k2_relat_1(C_793), B_792) | ~r1_tarski(k1_relat_1(C_793), A_794) | ~v1_relat_1(C_793))), inference(resolution, [status(thm)], [c_60, c_4308])).
% 8.29/2.82  tff(c_5974, plain, (![B_792, A_794]: (k1_xboole_0=B_792 | v1_funct_2('#skF_6', A_794, B_792) | k1_relset_1(A_794, B_792, '#skF_6')!=A_794 | ~r1_tarski('#skF_5', B_792) | ~r1_tarski(k1_relat_1('#skF_6'), A_794) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4119, c_5970])).
% 8.29/2.82  tff(c_6034, plain, (![B_803, A_804]: (k1_xboole_0=B_803 | v1_funct_2('#skF_6', A_804, B_803) | k1_relset_1(A_804, B_803, '#skF_6')!=A_804 | ~r1_tarski('#skF_5', B_803) | ~r1_tarski('#skF_3', A_804))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_4464, c_5974])).
% 8.29/2.82  tff(c_6043, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_3', '#skF_5', '#skF_6')!='#skF_3' | ~r1_tarski('#skF_5', '#skF_5') | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_6034, c_155])).
% 8.29/2.82  tff(c_6048, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_5377, c_6043])).
% 8.29/2.82  tff(c_6050, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4120, c_6048])).
% 8.29/2.82  tff(c_6051, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_183])).
% 8.29/2.82  tff(c_6579, plain, (![A_903, B_904, C_905]: (k1_relset_1(A_903, B_904, C_905)=k1_relat_1(C_905) | ~m1_subset_1(C_905, k1_zfmisc_1(k2_zfmisc_1(A_903, B_904))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.29/2.82  tff(c_6582, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_6579])).
% 8.29/2.82  tff(c_6590, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6051, c_6582])).
% 8.29/2.82  tff(c_6818, plain, (![B_946, A_947, C_948]: (k1_xboole_0=B_946 | k1_relset_1(A_947, B_946, C_948)=A_947 | ~v1_funct_2(C_948, A_947, B_946) | ~m1_subset_1(C_948, k1_zfmisc_1(k2_zfmisc_1(A_947, B_946))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.29/2.82  tff(c_6824, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_6818])).
% 8.29/2.82  tff(c_6834, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_6590, c_6824])).
% 8.29/2.82  tff(c_6835, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_93, c_6834])).
% 8.29/2.82  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.29/2.82  tff(c_6884, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6835, c_8])).
% 8.29/2.82  tff(c_30, plain, (![B_15]: (k2_zfmisc_1(k1_xboole_0, B_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.29/2.82  tff(c_6881, plain, (![B_15]: (k2_zfmisc_1('#skF_3', B_15)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6835, c_6835, c_30])).
% 8.29/2.82  tff(c_6462, plain, (![C_881, B_882, A_883]: (~v1_xboole_0(C_881) | ~m1_subset_1(B_882, k1_zfmisc_1(C_881)) | ~r2_hidden(A_883, B_882))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.29/2.82  tff(c_6465, plain, (![A_883]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4')) | ~r2_hidden(A_883, '#skF_6'))), inference(resolution, [status(thm)], [c_80, c_6462])).
% 8.29/2.82  tff(c_6466, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_6465])).
% 8.29/2.82  tff(c_7047, plain, (~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6881, c_6466])).
% 8.29/2.82  tff(c_7051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6884, c_7047])).
% 8.29/2.82  tff(c_7054, plain, (![A_959]: (~r2_hidden(A_959, '#skF_6'))), inference(splitRight, [status(thm)], [c_6465])).
% 8.29/2.82  tff(c_7070, plain, (![B_960]: (r1_xboole_0('#skF_6', B_960))), inference(resolution, [status(thm)], [c_14, c_7054])).
% 8.29/2.82  tff(c_24, plain, (![A_13]: (~r1_xboole_0(A_13, A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.29/2.82  tff(c_7078, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_7070, c_24])).
% 8.29/2.82  tff(c_7123, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7078, c_93])).
% 8.29/2.82  tff(c_7113, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7078, c_6051])).
% 8.29/2.82  tff(c_8136, plain, (![A_1081, B_1082, C_1083]: (k1_relset_1(A_1081, B_1082, C_1083)=k1_relat_1(C_1083) | ~m1_subset_1(C_1083, k1_zfmisc_1(k2_zfmisc_1(A_1081, B_1082))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.29/2.82  tff(c_8145, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_8136])).
% 8.29/2.82  tff(c_8147, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7113, c_8145])).
% 8.29/2.82  tff(c_72, plain, (![B_45, A_44, C_46]: (k1_xboole_0=B_45 | k1_relset_1(A_44, B_45, C_46)=A_44 | ~v1_funct_2(C_46, A_44, B_45) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.29/2.82  tff(c_8505, plain, (![B_1133, A_1134, C_1135]: (B_1133='#skF_6' | k1_relset_1(A_1134, B_1133, C_1135)=A_1134 | ~v1_funct_2(C_1135, A_1134, B_1133) | ~m1_subset_1(C_1135, k1_zfmisc_1(k2_zfmisc_1(A_1134, B_1133))))), inference(demodulation, [status(thm), theory('equality')], [c_7078, c_72])).
% 8.29/2.82  tff(c_8517, plain, ('#skF_6'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_8505])).
% 8.29/2.82  tff(c_8522, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_8147, c_8517])).
% 8.29/2.82  tff(c_8523, plain, ('#skF_6'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_7123, c_8522])).
% 8.29/2.82  tff(c_7313, plain, (![A_978, B_979, C_980]: (k1_relset_1(A_978, B_979, C_980)=k1_relat_1(C_980) | ~m1_subset_1(C_980, k1_zfmisc_1(k2_zfmisc_1(A_978, B_979))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.29/2.82  tff(c_7322, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_7313])).
% 8.29/2.82  tff(c_7324, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7113, c_7322])).
% 8.29/2.82  tff(c_7810, plain, (![B_1063, A_1064, C_1065]: (B_1063='#skF_6' | k1_relset_1(A_1064, B_1063, C_1065)=A_1064 | ~v1_funct_2(C_1065, A_1064, B_1063) | ~m1_subset_1(C_1065, k1_zfmisc_1(k2_zfmisc_1(A_1064, B_1063))))), inference(demodulation, [status(thm), theory('equality')], [c_7078, c_72])).
% 8.29/2.82  tff(c_7822, plain, ('#skF_6'='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_80, c_7810])).
% 8.29/2.82  tff(c_7827, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_7324, c_7822])).
% 8.29/2.82  tff(c_7828, plain, ('#skF_6'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_7123, c_7827])).
% 8.29/2.82  tff(c_7121, plain, (![B_15]: (k2_zfmisc_1('#skF_6', B_15)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7078, c_7078, c_30])).
% 8.29/2.82  tff(c_7870, plain, (![B_15]: (k2_zfmisc_1('#skF_3', B_15)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7828, c_7828, c_7121])).
% 8.29/2.82  tff(c_7884, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_7828, c_80])).
% 8.29/2.82  tff(c_8038, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7870, c_7884])).
% 8.29/2.82  tff(c_28, plain, (![A_14]: (k2_zfmisc_1(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.29/2.82  tff(c_62, plain, (![A_44]: (v1_funct_2(k1_xboole_0, A_44, k1_xboole_0) | k1_xboole_0=A_44 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_44, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.29/2.82  tff(c_90, plain, (![A_44]: (v1_funct_2(k1_xboole_0, A_44, k1_xboole_0) | k1_xboole_0=A_44 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_62])).
% 8.29/2.82  tff(c_7219, plain, (![A_44]: (v1_funct_2('#skF_6', A_44, '#skF_6') | A_44='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_7078, c_7078, c_7078, c_7078, c_7078, c_90])).
% 8.29/2.82  tff(c_7220, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_7219])).
% 8.29/2.82  tff(c_7868, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7828, c_7828, c_7220])).
% 8.29/2.82  tff(c_8133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8038, c_7868])).
% 8.29/2.82  tff(c_8135, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(splitRight, [status(thm)], [c_7219])).
% 8.29/2.82  tff(c_8448, plain, (![B_1124, C_1125]: (k1_relset_1('#skF_6', B_1124, C_1125)=k1_relat_1(C_1125) | ~m1_subset_1(C_1125, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_7121, c_8136])).
% 8.29/2.82  tff(c_8450, plain, (![B_1124]: (k1_relset_1('#skF_6', B_1124, '#skF_6')=k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_8135, c_8448])).
% 8.29/2.82  tff(c_8452, plain, (![B_1124]: (k1_relset_1('#skF_6', B_1124, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7113, c_8450])).
% 8.29/2.82  tff(c_66, plain, (![C_46, B_45]: (v1_funct_2(C_46, k1_xboole_0, B_45) | k1_relset_1(k1_xboole_0, B_45, C_46)!=k1_xboole_0 | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_45))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 8.29/2.82  tff(c_88, plain, (![C_46, B_45]: (v1_funct_2(C_46, k1_xboole_0, B_45) | k1_relset_1(k1_xboole_0, B_45, C_46)!=k1_xboole_0 | ~m1_subset_1(C_46, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_66])).
% 8.29/2.82  tff(c_8389, plain, (![C_1113, B_1114]: (v1_funct_2(C_1113, '#skF_6', B_1114) | k1_relset_1('#skF_6', B_1114, C_1113)!='#skF_6' | ~m1_subset_1(C_1113, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_7078, c_7078, c_7078, c_7078, c_88])).
% 8.29/2.82  tff(c_8392, plain, (![B_1114]: (v1_funct_2('#skF_6', '#skF_6', B_1114) | k1_relset_1('#skF_6', B_1114, '#skF_6')!='#skF_6')), inference(resolution, [status(thm)], [c_8135, c_8389])).
% 8.29/2.82  tff(c_8454, plain, (![B_1114]: (v1_funct_2('#skF_6', '#skF_6', B_1114))), inference(demodulation, [status(thm), theory('equality')], [c_8452, c_8392])).
% 8.29/2.82  tff(c_8528, plain, (![B_1114]: (v1_funct_2('#skF_3', '#skF_3', B_1114))), inference(demodulation, [status(thm), theory('equality')], [c_8523, c_8523, c_8454])).
% 8.29/2.82  tff(c_8569, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8523, c_155])).
% 8.29/2.82  tff(c_8816, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8528, c_8569])).
% 8.29/2.82  tff(c_8817, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_5')))), inference(splitRight, [status(thm)], [c_86])).
% 8.29/2.82  tff(c_9429, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~r1_tarski(k1_relat_1('#skF_6'), '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_9409, c_8817])).
% 8.29/2.82  tff(c_9446, plain, (~r1_tarski(k1_relat_1('#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9088, c_9364, c_9429])).
% 8.29/2.82  tff(c_9449, plain, (~v4_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_9446])).
% 8.29/2.82  tff(c_9453, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9088, c_9157, c_9449])).
% 8.29/2.82  tff(c_9455, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_76])).
% 8.29/2.82  tff(c_9477, plain, (![A_1278]: (k2_zfmisc_1(A_1278, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9455, c_9455, c_28])).
% 8.29/2.82  tff(c_9481, plain, (v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_9477, c_40])).
% 8.29/2.82  tff(c_46, plain, (![A_29]: (k1_relat_1(A_29)=k1_xboole_0 | k2_relat_1(A_29)!=k1_xboole_0 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.29/2.82  tff(c_9558, plain, (![A_1292]: (k1_relat_1(A_1292)='#skF_4' | k2_relat_1(A_1292)!='#skF_4' | ~v1_relat_1(A_1292))), inference(demodulation, [status(thm), theory('equality')], [c_9455, c_9455, c_46])).
% 8.29/2.82  tff(c_9565, plain, (k1_relat_1('#skF_4')='#skF_4' | k2_relat_1('#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_9481, c_9558])).
% 8.29/2.82  tff(c_9567, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_9565])).
% 8.29/2.82  tff(c_50, plain, (![B_31, A_30]: (r1_tarski(k7_relat_1(B_31, A_30), B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.29/2.82  tff(c_9454, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_76])).
% 8.29/2.82  tff(c_9462, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9455, c_9454])).
% 8.29/2.82  tff(c_9457, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9454, c_8])).
% 8.29/2.82  tff(c_9467, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9462, c_9457])).
% 8.29/2.82  tff(c_9476, plain, (![A_14]: (k2_zfmisc_1(A_14, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9455, c_9455, c_28])).
% 8.29/2.82  tff(c_9512, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9476, c_9462, c_80])).
% 8.29/2.82  tff(c_9648, plain, (![C_1310, B_1311, A_1312]: (~v1_xboole_0(C_1310) | ~m1_subset_1(B_1311, k1_zfmisc_1(C_1310)) | ~r2_hidden(A_1312, B_1311))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.29/2.82  tff(c_9650, plain, (![A_1312]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_1312, '#skF_6'))), inference(resolution, [status(thm)], [c_9512, c_9648])).
% 8.29/2.82  tff(c_9654, plain, (![A_1313]: (~r2_hidden(A_1313, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_9467, c_9650])).
% 8.29/2.82  tff(c_9684, plain, (![B_1318]: (r1_xboole_0('#skF_6', B_1318))), inference(resolution, [status(thm)], [c_14, c_9654])).
% 8.29/2.82  tff(c_9505, plain, (![A_13]: (~r1_xboole_0(A_13, A_13) | A_13='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9455, c_24])).
% 8.29/2.82  tff(c_9689, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_9684, c_9505])).
% 8.29/2.82  tff(c_9670, plain, (![B_1314]: (r1_tarski('#skF_6', B_1314))), inference(resolution, [status(thm)], [c_6, c_9654])).
% 8.29/2.82  tff(c_16, plain, (![B_12, A_11]: (B_12=A_11 | ~r1_tarski(B_12, A_11) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.29/2.82  tff(c_9673, plain, (![B_1314]: (B_1314='#skF_6' | ~r1_tarski(B_1314, '#skF_6'))), inference(resolution, [status(thm)], [c_9670, c_16])).
% 8.29/2.82  tff(c_9772, plain, (![B_1326]: (B_1326='#skF_4' | ~r1_tarski(B_1326, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9689, c_9689, c_9673])).
% 8.29/2.82  tff(c_9784, plain, (![A_30]: (k7_relat_1('#skF_4', A_30)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_9772])).
% 8.29/2.82  tff(c_9797, plain, (![A_1327]: (k7_relat_1('#skF_4', A_1327)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9481, c_9784])).
% 8.29/2.82  tff(c_42, plain, (![B_27, A_26]: (k2_relat_1(k7_relat_1(B_27, A_26))=k9_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.29/2.82  tff(c_9802, plain, (![A_1327]: (k9_relat_1('#skF_4', A_1327)=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9797, c_42])).
% 8.29/2.82  tff(c_9814, plain, (![A_1328]: (k9_relat_1('#skF_4', A_1328)=k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_9481, c_9802])).
% 8.29/2.82  tff(c_44, plain, (![A_28]: (k9_relat_1(A_28, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.29/2.82  tff(c_9514, plain, (![A_1281]: (k9_relat_1(A_1281, '#skF_4')='#skF_4' | ~v1_relat_1(A_1281))), inference(demodulation, [status(thm), theory('equality')], [c_9455, c_9455, c_44])).
% 8.29/2.82  tff(c_9521, plain, (k9_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_9481, c_9514])).
% 8.29/2.82  tff(c_9818, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_9814, c_9521])).
% 8.29/2.82  tff(c_9825, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9567, c_9818])).
% 8.29/2.82  tff(c_9826, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_9565])).
% 8.29/2.82  tff(c_10279, plain, (![C_1403, B_1404, A_1405]: (~v1_xboole_0(C_1403) | ~m1_subset_1(B_1404, k1_zfmisc_1(C_1403)) | ~r2_hidden(A_1405, B_1404))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.29/2.82  tff(c_10281, plain, (![A_1405]: (~v1_xboole_0('#skF_4') | ~r2_hidden(A_1405, '#skF_6'))), inference(resolution, [status(thm)], [c_9512, c_10279])).
% 8.29/2.82  tff(c_10285, plain, (![A_1406]: (~r2_hidden(A_1406, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_9467, c_10281])).
% 8.29/2.82  tff(c_10301, plain, (![B_1407]: (r1_tarski('#skF_6', B_1407))), inference(resolution, [status(thm)], [c_6, c_10285])).
% 8.29/2.82  tff(c_9456, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9454, c_9454, c_22])).
% 8.29/2.82  tff(c_9473, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9462, c_9462, c_9456])).
% 8.29/2.82  tff(c_10178, plain, (![A_1389, B_1390, C_1391]: (~r1_xboole_0(A_1389, B_1390) | ~r2_hidden(C_1391, B_1390) | ~r2_hidden(C_1391, A_1389))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.29/2.82  tff(c_10182, plain, (![C_1392]: (~r2_hidden(C_1392, '#skF_4'))), inference(resolution, [status(thm)], [c_9473, c_10178])).
% 8.29/2.82  tff(c_10200, plain, (![B_1393]: (r1_tarski('#skF_4', B_1393))), inference(resolution, [status(thm)], [c_6, c_10182])).
% 8.29/2.82  tff(c_10203, plain, (![B_1393]: (B_1393='#skF_4' | ~r1_tarski(B_1393, '#skF_4'))), inference(resolution, [status(thm)], [c_10200, c_16])).
% 8.29/2.82  tff(c_10308, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_10301, c_10203])).
% 8.29/2.82  tff(c_10319, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_10308, c_9512])).
% 8.29/2.82  tff(c_9486, plain, (![B_15]: (k2_zfmisc_1('#skF_4', B_15)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9455, c_9455, c_30])).
% 8.29/2.82  tff(c_10533, plain, (![A_1437, B_1438, C_1439]: (k1_relset_1(A_1437, B_1438, C_1439)=k1_relat_1(C_1439) | ~m1_subset_1(C_1439, k1_zfmisc_1(k2_zfmisc_1(A_1437, B_1438))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.29/2.82  tff(c_10547, plain, (![B_1442, C_1443]: (k1_relset_1('#skF_4', B_1442, C_1443)=k1_relat_1(C_1443) | ~m1_subset_1(C_1443, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_9486, c_10533])).
% 8.29/2.82  tff(c_10549, plain, (![B_1442]: (k1_relset_1('#skF_4', B_1442, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_10319, c_10547])).
% 8.29/2.82  tff(c_10551, plain, (![B_1442]: (k1_relset_1('#skF_4', B_1442, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9826, c_10549])).
% 8.29/2.82  tff(c_10871, plain, (![C_1492, B_1493]: (v1_funct_2(C_1492, '#skF_4', B_1493) | k1_relset_1('#skF_4', B_1493, C_1492)!='#skF_4' | ~m1_subset_1(C_1492, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_9455, c_9455, c_9455, c_9455, c_88])).
% 8.29/2.82  tff(c_10873, plain, (![B_1493]: (v1_funct_2('#skF_4', '#skF_4', B_1493) | k1_relset_1('#skF_4', B_1493, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_10319, c_10871])).
% 8.29/2.82  tff(c_10876, plain, (![B_1493]: (v1_funct_2('#skF_4', '#skF_4', B_1493))), inference(demodulation, [status(thm), theory('equality')], [c_10551, c_10873])).
% 8.29/2.82  tff(c_9542, plain, (~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_9462, c_9512, c_9486, c_9462, c_86])).
% 8.29/2.82  tff(c_10318, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10308, c_9542])).
% 8.29/2.82  tff(c_10880, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10876, c_10318])).
% 8.29/2.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.29/2.82  
% 8.29/2.82  Inference rules
% 8.29/2.82  ----------------------
% 8.29/2.82  #Ref     : 0
% 8.29/2.82  #Sup     : 2296
% 8.29/2.82  #Fact    : 0
% 8.29/2.82  #Define  : 0
% 8.29/2.82  #Split   : 44
% 8.29/2.82  #Chain   : 0
% 8.29/2.82  #Close   : 0
% 8.29/2.82  
% 8.29/2.82  Ordering : KBO
% 8.29/2.82  
% 8.29/2.82  Simplification rules
% 8.29/2.82  ----------------------
% 8.29/2.82  #Subsume      : 424
% 8.29/2.82  #Demod        : 2152
% 8.29/2.82  #Tautology    : 985
% 8.29/2.82  #SimpNegUnit  : 41
% 8.29/2.82  #BackRed      : 358
% 8.29/2.82  
% 8.29/2.82  #Partial instantiations: 0
% 8.29/2.82  #Strategies tried      : 1
% 8.29/2.82  
% 8.29/2.82  Timing (in seconds)
% 8.29/2.82  ----------------------
% 8.29/2.83  Preprocessing        : 0.36
% 8.29/2.83  Parsing              : 0.20
% 8.29/2.83  CNF conversion       : 0.03
% 8.29/2.83  Main loop            : 1.63
% 8.29/2.83  Inferencing          : 0.56
% 8.29/2.83  Reduction            : 0.52
% 8.29/2.83  Demodulation         : 0.35
% 8.29/2.83  BG Simplification    : 0.06
% 8.29/2.83  Subsumption          : 0.33
% 8.29/2.83  Abstraction          : 0.06
% 8.29/2.83  MUC search           : 0.00
% 8.29/2.83  Cooper               : 0.00
% 8.29/2.83  Total                : 2.07
% 8.29/2.83  Index Insertion      : 0.00
% 8.29/2.83  Index Deletion       : 0.00
% 8.29/2.83  Index Matching       : 0.00
% 8.29/2.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
