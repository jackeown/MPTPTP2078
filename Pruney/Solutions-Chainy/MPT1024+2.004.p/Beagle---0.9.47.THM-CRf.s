%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:22 EST 2020

% Result     : Theorem 4.41s
% Output     : CNFRefutation 4.41s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 289 expanded)
%              Number of leaves         :   38 ( 115 expanded)
%              Depth                    :   13
%              Number of atoms          :  179 ( 757 expanded)
%              Number of equality atoms :   21 (  89 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_77,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_86,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_77])).

tff(c_144,plain,(
    ! [C_66,A_67,B_68] :
      ( v4_relat_1(C_66,A_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_153,plain,(
    v4_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_144])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_772,plain,(
    ! [A_210,B_211,C_212,D_213] :
      ( k7_relset_1(A_210,B_211,C_212,D_213) = k9_relat_1(C_212,D_213)
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_783,plain,(
    ! [D_213] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_213) = k9_relat_1('#skF_6',D_213) ),
    inference(resolution,[status(thm)],[c_46,c_772])).

tff(c_44,plain,(
    r2_hidden('#skF_7',k7_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_786,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_783,c_44])).

tff(c_26,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden('#skF_2'(A_17,B_18,C_19),k1_relat_1(C_19))
      | ~ r2_hidden(A_17,k9_relat_1(C_19,B_18))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_972,plain,(
    ! [A_233,B_234,C_235] :
      ( r2_hidden(k4_tarski('#skF_2'(A_233,B_234,C_235),A_233),C_235)
      | ~ r2_hidden(A_233,k9_relat_1(C_235,B_234))
      | ~ v1_relat_1(C_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,(
    ! [C_25,A_23,B_24] :
      ( k1_funct_1(C_25,A_23) = B_24
      | ~ r2_hidden(k4_tarski(A_23,B_24),C_25)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1346,plain,(
    ! [C_278,A_279,B_280] :
      ( k1_funct_1(C_278,'#skF_2'(A_279,B_280,C_278)) = A_279
      | ~ v1_funct_1(C_278)
      | ~ r2_hidden(A_279,k9_relat_1(C_278,B_280))
      | ~ v1_relat_1(C_278) ) ),
    inference(resolution,[status(thm)],[c_972,c_30])).

tff(c_1356,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_786,c_1346])).

tff(c_1371,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_50,c_1356])).

tff(c_28,plain,(
    ! [A_23,C_25] :
      ( r2_hidden(k4_tarski(A_23,k1_funct_1(C_25,A_23)),C_25)
      | ~ r2_hidden(A_23,k1_relat_1(C_25))
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1378,plain,
    ( r2_hidden(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1371,c_28])).

tff(c_1382,plain,
    ( r2_hidden(k4_tarski('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_50,c_1378])).

tff(c_1539,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1382])).

tff(c_1542,plain,
    ( ~ r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_1539])).

tff(c_1549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_786,c_1542])).

tff(c_1551,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_5','#skF_6'),k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1382])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_182,plain,(
    ! [A_77,C_78,B_79] :
      ( m1_subset_1(A_77,C_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(C_78))
      | ~ r2_hidden(A_77,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_187,plain,(
    ! [A_77,B_11,A_10] :
      ( m1_subset_1(A_77,B_11)
      | ~ r2_hidden(A_77,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_182])).

tff(c_1591,plain,(
    ! [B_305] :
      ( m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),B_305)
      | ~ r1_tarski(k1_relat_1('#skF_6'),B_305) ) ),
    inference(resolution,[status(thm)],[c_1551,c_187])).

tff(c_1595,plain,(
    ! [A_15] :
      ( m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),A_15)
      | ~ v4_relat_1('#skF_6',A_15)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_18,c_1591])).

tff(c_1599,plain,(
    ! [A_306] :
      ( m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),A_306)
      | ~ v4_relat_1('#skF_6',A_306) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1595])).

tff(c_124,plain,(
    ! [B_61,A_62] :
      ( r1_tarski(k1_relat_1(B_61),A_62)
      | ~ v4_relat_1(B_61,A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_103,plain,(
    ! [B_57,A_58] :
      ( v1_xboole_0(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_110,plain,(
    ! [A_10,B_11] :
      ( v1_xboole_0(A_10)
      | ~ v1_xboole_0(B_11)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_103])).

tff(c_254,plain,(
    ! [B_94,A_95] :
      ( v1_xboole_0(k1_relat_1(B_94))
      | ~ v1_xboole_0(A_95)
      | ~ v4_relat_1(B_94,A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(resolution,[status(thm)],[c_124,c_110])).

tff(c_256,plain,
    ( v1_xboole_0(k1_relat_1('#skF_6'))
    | ~ v1_xboole_0('#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_153,c_254])).

tff(c_259,plain,
    ( v1_xboole_0(k1_relat_1('#skF_6'))
    | ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_256])).

tff(c_260,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_621,plain,(
    ! [A_171,B_172,C_173] :
      ( r2_hidden('#skF_2'(A_171,B_172,C_173),B_172)
      | ~ r2_hidden(A_171,k9_relat_1(C_173,B_172))
      | ~ v1_relat_1(C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_42,plain,(
    ! [F_40] :
      ( k1_funct_1('#skF_6',F_40) != '#skF_7'
      | ~ r2_hidden(F_40,'#skF_5')
      | ~ r2_hidden(F_40,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_667,plain,(
    ! [A_182,C_183] :
      ( k1_funct_1('#skF_6','#skF_2'(A_182,'#skF_5',C_183)) != '#skF_7'
      | ~ r2_hidden('#skF_2'(A_182,'#skF_5',C_183),'#skF_3')
      | ~ r2_hidden(A_182,k9_relat_1(C_183,'#skF_5'))
      | ~ v1_relat_1(C_183) ) ),
    inference(resolution,[status(thm)],[c_621,c_42])).

tff(c_670,plain,(
    ! [A_182,C_183] :
      ( k1_funct_1('#skF_6','#skF_2'(A_182,'#skF_5',C_183)) != '#skF_7'
      | ~ r2_hidden(A_182,k9_relat_1(C_183,'#skF_5'))
      | ~ v1_relat_1(C_183)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1('#skF_2'(A_182,'#skF_5',C_183),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_667])).

tff(c_1097,plain,(
    ! [A_245,C_246] :
      ( k1_funct_1('#skF_6','#skF_2'(A_245,'#skF_5',C_246)) != '#skF_7'
      | ~ r2_hidden(A_245,k9_relat_1(C_246,'#skF_5'))
      | ~ v1_relat_1(C_246)
      | ~ m1_subset_1('#skF_2'(A_245,'#skF_5',C_246),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_670])).

tff(c_1108,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ v1_relat_1('#skF_6')
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_786,c_1097])).

tff(c_1125,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7'
    | ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1108])).

tff(c_1130,plain,(
    ~ m1_subset_1('#skF_2'('#skF_7','#skF_5','#skF_6'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1125])).

tff(c_1602,plain,(
    ~ v4_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_1599,c_1130])).

tff(c_1636,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_1602])).

tff(c_1637,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1125])).

tff(c_1993,plain,(
    ! [C_356,A_357,B_358] :
      ( k1_funct_1(C_356,'#skF_2'(A_357,B_358,C_356)) = A_357
      | ~ v1_funct_1(C_356)
      | ~ r2_hidden(A_357,k9_relat_1(C_356,B_358))
      | ~ v1_relat_1(C_356) ) ),
    inference(resolution,[status(thm)],[c_972,c_30])).

tff(c_2003,plain,
    ( k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7'
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_786,c_1993])).

tff(c_2018,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_7','#skF_5','#skF_6')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_50,c_2003])).

tff(c_2020,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1637,c_2018])).

tff(c_2021,plain,(
    v1_xboole_0(k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_2179,plain,(
    ! [A_404,B_405,C_406,D_407] :
      ( k7_relset_1(A_404,B_405,C_406,D_407) = k9_relat_1(C_406,D_407)
      | ~ m1_subset_1(C_406,k1_zfmisc_1(k2_zfmisc_1(A_404,B_405))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2190,plain,(
    ! [D_407] : k7_relset_1('#skF_3','#skF_4','#skF_6',D_407) = k9_relat_1('#skF_6',D_407) ),
    inference(resolution,[status(thm)],[c_46,c_2179])).

tff(c_2193,plain,(
    r2_hidden('#skF_7',k9_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2190,c_44])).

tff(c_2203,plain,(
    ! [A_409,B_410,C_411] :
      ( r2_hidden('#skF_2'(A_409,B_410,C_411),k1_relat_1(C_411))
      | ~ r2_hidden(A_409,k9_relat_1(C_411,B_410))
      | ~ v1_relat_1(C_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2231,plain,(
    ! [C_413,A_414,B_415] :
      ( ~ v1_xboole_0(k1_relat_1(C_413))
      | ~ r2_hidden(A_414,k9_relat_1(C_413,B_415))
      | ~ v1_relat_1(C_413) ) ),
    inference(resolution,[status(thm)],[c_2203,c_2])).

tff(c_2234,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2193,c_2231])).

tff(c_2250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2021,c_2234])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:57:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.41/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.41/1.78  
% 4.41/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.41/1.78  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 4.41/1.78  
% 4.41/1.78  %Foreground sorts:
% 4.41/1.78  
% 4.41/1.78  
% 4.41/1.78  %Background operators:
% 4.41/1.78  
% 4.41/1.78  
% 4.41/1.78  %Foreground operators:
% 4.41/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.41/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.41/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.41/1.78  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.41/1.78  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.41/1.78  tff('#skF_7', type, '#skF_7': $i).
% 4.41/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.41/1.78  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.41/1.78  tff('#skF_5', type, '#skF_5': $i).
% 4.41/1.78  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.41/1.78  tff('#skF_6', type, '#skF_6': $i).
% 4.41/1.78  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.41/1.78  tff('#skF_3', type, '#skF_3': $i).
% 4.41/1.78  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.41/1.78  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.41/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.41/1.78  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.41/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.41/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.41/1.78  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.41/1.78  tff('#skF_4', type, '#skF_4': $i).
% 4.41/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.41/1.78  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.41/1.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.41/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.41/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.41/1.78  
% 4.41/1.80  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 4.41/1.80  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.41/1.80  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.41/1.80  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.41/1.80  tff(f_95, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.41/1.80  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 4.41/1.80  tff(f_81, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 4.41/1.80  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.41/1.80  tff(f_54, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.41/1.80  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 4.41/1.80  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.41/1.80  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.41/1.80  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.41/1.80  tff(c_77, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.41/1.80  tff(c_86, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_77])).
% 4.41/1.80  tff(c_144, plain, (![C_66, A_67, B_68]: (v4_relat_1(C_66, A_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.41/1.80  tff(c_153, plain, (v4_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_144])).
% 4.41/1.80  tff(c_18, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.41/1.80  tff(c_772, plain, (![A_210, B_211, C_212, D_213]: (k7_relset_1(A_210, B_211, C_212, D_213)=k9_relat_1(C_212, D_213) | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.41/1.80  tff(c_783, plain, (![D_213]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_213)=k9_relat_1('#skF_6', D_213))), inference(resolution, [status(thm)], [c_46, c_772])).
% 4.41/1.80  tff(c_44, plain, (r2_hidden('#skF_7', k7_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.41/1.80  tff(c_786, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_783, c_44])).
% 4.41/1.80  tff(c_26, plain, (![A_17, B_18, C_19]: (r2_hidden('#skF_2'(A_17, B_18, C_19), k1_relat_1(C_19)) | ~r2_hidden(A_17, k9_relat_1(C_19, B_18)) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.41/1.80  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.41/1.80  tff(c_972, plain, (![A_233, B_234, C_235]: (r2_hidden(k4_tarski('#skF_2'(A_233, B_234, C_235), A_233), C_235) | ~r2_hidden(A_233, k9_relat_1(C_235, B_234)) | ~v1_relat_1(C_235))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.41/1.80  tff(c_30, plain, (![C_25, A_23, B_24]: (k1_funct_1(C_25, A_23)=B_24 | ~r2_hidden(k4_tarski(A_23, B_24), C_25) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.41/1.80  tff(c_1346, plain, (![C_278, A_279, B_280]: (k1_funct_1(C_278, '#skF_2'(A_279, B_280, C_278))=A_279 | ~v1_funct_1(C_278) | ~r2_hidden(A_279, k9_relat_1(C_278, B_280)) | ~v1_relat_1(C_278))), inference(resolution, [status(thm)], [c_972, c_30])).
% 4.41/1.80  tff(c_1356, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_786, c_1346])).
% 4.41/1.80  tff(c_1371, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_50, c_1356])).
% 4.41/1.80  tff(c_28, plain, (![A_23, C_25]: (r2_hidden(k4_tarski(A_23, k1_funct_1(C_25, A_23)), C_25) | ~r2_hidden(A_23, k1_relat_1(C_25)) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.41/1.80  tff(c_1378, plain, (r2_hidden(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1371, c_28])).
% 4.41/1.80  tff(c_1382, plain, (r2_hidden(k4_tarski('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_7'), '#skF_6') | ~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_50, c_1378])).
% 4.41/1.80  tff(c_1539, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_1382])).
% 4.41/1.80  tff(c_1542, plain, (~r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_1539])).
% 4.41/1.80  tff(c_1549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_786, c_1542])).
% 4.41/1.80  tff(c_1551, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_5', '#skF_6'), k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_1382])).
% 4.41/1.80  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.41/1.80  tff(c_182, plain, (![A_77, C_78, B_79]: (m1_subset_1(A_77, C_78) | ~m1_subset_1(B_79, k1_zfmisc_1(C_78)) | ~r2_hidden(A_77, B_79))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.41/1.80  tff(c_187, plain, (![A_77, B_11, A_10]: (m1_subset_1(A_77, B_11) | ~r2_hidden(A_77, A_10) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_12, c_182])).
% 4.41/1.80  tff(c_1591, plain, (![B_305]: (m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), B_305) | ~r1_tarski(k1_relat_1('#skF_6'), B_305))), inference(resolution, [status(thm)], [c_1551, c_187])).
% 4.41/1.80  tff(c_1595, plain, (![A_15]: (m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), A_15) | ~v4_relat_1('#skF_6', A_15) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_18, c_1591])).
% 4.41/1.80  tff(c_1599, plain, (![A_306]: (m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), A_306) | ~v4_relat_1('#skF_6', A_306))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1595])).
% 4.41/1.80  tff(c_124, plain, (![B_61, A_62]: (r1_tarski(k1_relat_1(B_61), A_62) | ~v4_relat_1(B_61, A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.41/1.80  tff(c_103, plain, (![B_57, A_58]: (v1_xboole_0(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.41/1.80  tff(c_110, plain, (![A_10, B_11]: (v1_xboole_0(A_10) | ~v1_xboole_0(B_11) | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_12, c_103])).
% 4.41/1.80  tff(c_254, plain, (![B_94, A_95]: (v1_xboole_0(k1_relat_1(B_94)) | ~v1_xboole_0(A_95) | ~v4_relat_1(B_94, A_95) | ~v1_relat_1(B_94))), inference(resolution, [status(thm)], [c_124, c_110])).
% 4.41/1.80  tff(c_256, plain, (v1_xboole_0(k1_relat_1('#skF_6')) | ~v1_xboole_0('#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_153, c_254])).
% 4.41/1.80  tff(c_259, plain, (v1_xboole_0(k1_relat_1('#skF_6')) | ~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_256])).
% 4.41/1.80  tff(c_260, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_259])).
% 4.41/1.80  tff(c_8, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.41/1.80  tff(c_621, plain, (![A_171, B_172, C_173]: (r2_hidden('#skF_2'(A_171, B_172, C_173), B_172) | ~r2_hidden(A_171, k9_relat_1(C_173, B_172)) | ~v1_relat_1(C_173))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.41/1.80  tff(c_42, plain, (![F_40]: (k1_funct_1('#skF_6', F_40)!='#skF_7' | ~r2_hidden(F_40, '#skF_5') | ~r2_hidden(F_40, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.41/1.80  tff(c_667, plain, (![A_182, C_183]: (k1_funct_1('#skF_6', '#skF_2'(A_182, '#skF_5', C_183))!='#skF_7' | ~r2_hidden('#skF_2'(A_182, '#skF_5', C_183), '#skF_3') | ~r2_hidden(A_182, k9_relat_1(C_183, '#skF_5')) | ~v1_relat_1(C_183))), inference(resolution, [status(thm)], [c_621, c_42])).
% 4.41/1.80  tff(c_670, plain, (![A_182, C_183]: (k1_funct_1('#skF_6', '#skF_2'(A_182, '#skF_5', C_183))!='#skF_7' | ~r2_hidden(A_182, k9_relat_1(C_183, '#skF_5')) | ~v1_relat_1(C_183) | v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_2'(A_182, '#skF_5', C_183), '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_667])).
% 4.41/1.80  tff(c_1097, plain, (![A_245, C_246]: (k1_funct_1('#skF_6', '#skF_2'(A_245, '#skF_5', C_246))!='#skF_7' | ~r2_hidden(A_245, k9_relat_1(C_246, '#skF_5')) | ~v1_relat_1(C_246) | ~m1_subset_1('#skF_2'(A_245, '#skF_5', C_246), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_260, c_670])).
% 4.41/1.80  tff(c_1108, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~v1_relat_1('#skF_6') | ~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(resolution, [status(thm)], [c_786, c_1097])).
% 4.41/1.80  tff(c_1125, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7' | ~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1108])).
% 4.41/1.80  tff(c_1130, plain, (~m1_subset_1('#skF_2'('#skF_7', '#skF_5', '#skF_6'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1125])).
% 4.41/1.80  tff(c_1602, plain, (~v4_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_1599, c_1130])).
% 4.41/1.80  tff(c_1636, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_153, c_1602])).
% 4.41/1.80  tff(c_1637, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))!='#skF_7'), inference(splitRight, [status(thm)], [c_1125])).
% 4.41/1.80  tff(c_1993, plain, (![C_356, A_357, B_358]: (k1_funct_1(C_356, '#skF_2'(A_357, B_358, C_356))=A_357 | ~v1_funct_1(C_356) | ~r2_hidden(A_357, k9_relat_1(C_356, B_358)) | ~v1_relat_1(C_356))), inference(resolution, [status(thm)], [c_972, c_30])).
% 4.41/1.80  tff(c_2003, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7' | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_786, c_1993])).
% 4.41/1.80  tff(c_2018, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_7', '#skF_5', '#skF_6'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_50, c_2003])).
% 4.41/1.80  tff(c_2020, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1637, c_2018])).
% 4.41/1.80  tff(c_2021, plain, (v1_xboole_0(k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_259])).
% 4.41/1.80  tff(c_2179, plain, (![A_404, B_405, C_406, D_407]: (k7_relset_1(A_404, B_405, C_406, D_407)=k9_relat_1(C_406, D_407) | ~m1_subset_1(C_406, k1_zfmisc_1(k2_zfmisc_1(A_404, B_405))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.41/1.80  tff(c_2190, plain, (![D_407]: (k7_relset_1('#skF_3', '#skF_4', '#skF_6', D_407)=k9_relat_1('#skF_6', D_407))), inference(resolution, [status(thm)], [c_46, c_2179])).
% 4.41/1.80  tff(c_2193, plain, (r2_hidden('#skF_7', k9_relat_1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2190, c_44])).
% 4.41/1.80  tff(c_2203, plain, (![A_409, B_410, C_411]: (r2_hidden('#skF_2'(A_409, B_410, C_411), k1_relat_1(C_411)) | ~r2_hidden(A_409, k9_relat_1(C_411, B_410)) | ~v1_relat_1(C_411))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.41/1.80  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.41/1.80  tff(c_2231, plain, (![C_413, A_414, B_415]: (~v1_xboole_0(k1_relat_1(C_413)) | ~r2_hidden(A_414, k9_relat_1(C_413, B_415)) | ~v1_relat_1(C_413))), inference(resolution, [status(thm)], [c_2203, c_2])).
% 4.41/1.80  tff(c_2234, plain, (~v1_xboole_0(k1_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2193, c_2231])).
% 4.41/1.80  tff(c_2250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_2021, c_2234])).
% 4.41/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.41/1.80  
% 4.41/1.80  Inference rules
% 4.41/1.80  ----------------------
% 4.41/1.80  #Ref     : 0
% 4.41/1.80  #Sup     : 436
% 4.41/1.80  #Fact    : 0
% 4.41/1.80  #Define  : 0
% 4.41/1.80  #Split   : 14
% 4.41/1.80  #Chain   : 0
% 4.41/1.80  #Close   : 0
% 4.41/1.80  
% 4.41/1.80  Ordering : KBO
% 4.41/1.80  
% 4.41/1.80  Simplification rules
% 4.41/1.80  ----------------------
% 4.41/1.80  #Subsume      : 80
% 4.41/1.80  #Demod        : 72
% 4.41/1.80  #Tautology    : 26
% 4.41/1.80  #SimpNegUnit  : 17
% 4.41/1.80  #BackRed      : 9
% 4.41/1.80  
% 4.41/1.80  #Partial instantiations: 0
% 4.41/1.80  #Strategies tried      : 1
% 4.41/1.80  
% 4.41/1.80  Timing (in seconds)
% 4.41/1.80  ----------------------
% 4.41/1.81  Preprocessing        : 0.33
% 4.41/1.81  Parsing              : 0.18
% 4.41/1.81  CNF conversion       : 0.02
% 4.41/1.81  Main loop            : 0.69
% 4.41/1.81  Inferencing          : 0.27
% 4.41/1.81  Reduction            : 0.16
% 4.41/1.81  Demodulation         : 0.11
% 4.41/1.81  BG Simplification    : 0.03
% 4.41/1.81  Subsumption          : 0.16
% 4.41/1.81  Abstraction          : 0.05
% 4.41/1.81  MUC search           : 0.00
% 4.41/1.81  Cooper               : 0.00
% 4.41/1.81  Total                : 1.06
% 4.41/1.81  Index Insertion      : 0.00
% 4.41/1.81  Index Deletion       : 0.00
% 4.41/1.81  Index Matching       : 0.00
% 4.41/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
