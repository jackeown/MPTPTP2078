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
% DateTime   : Thu Dec  3 10:16:36 EST 2020

% Result     : Theorem 6.71s
% Output     : CNFRefutation 6.87s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 219 expanded)
%              Number of leaves         :   47 (  96 expanded)
%              Depth                    :    8
%              Number of atoms          :  171 ( 522 expanded)
%              Number of equality atoms :   31 (  88 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_149,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_130,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_12,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_74,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_116,plain,(
    ! [B_98,A_99] :
      ( v1_relat_1(B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_99))
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_123,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_74,c_116])).

tff(c_127,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_123])).

tff(c_339,plain,(
    ! [A_174,B_175,C_176,D_177] :
      ( k7_relset_1(A_174,B_175,C_176,D_177) = k9_relat_1(C_176,D_177)
      | ~ m1_subset_1(C_176,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_346,plain,(
    ! [D_177] : k7_relset_1('#skF_7','#skF_8','#skF_10',D_177) = k9_relat_1('#skF_10',D_177) ),
    inference(resolution,[status(thm)],[c_74,c_339])).

tff(c_72,plain,(
    r2_hidden('#skF_11',k7_relset_1('#skF_7','#skF_8','#skF_10','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_350,plain,(
    r2_hidden('#skF_11',k9_relat_1('#skF_10','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_72])).

tff(c_298,plain,(
    ! [A_161,B_162,C_163] :
      ( r2_hidden('#skF_2'(A_161,B_162,C_163),k1_relat_1(C_163))
      | ~ r2_hidden(A_161,k9_relat_1(C_163,B_162))
      | ~ v1_relat_1(C_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_314,plain,(
    ! [C_163,A_161,B_162] :
      ( ~ v1_xboole_0(k1_relat_1(C_163))
      | ~ r2_hidden(A_161,k9_relat_1(C_163,B_162))
      | ~ v1_relat_1(C_163) ) ),
    inference(resolution,[status(thm)],[c_298,c_2])).

tff(c_383,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_350,c_314])).

tff(c_406,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_383])).

tff(c_78,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_144,plain,(
    ! [C_104,B_105,A_106] :
      ( v5_relat_1(C_104,B_105)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_106,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_153,plain,(
    v5_relat_1('#skF_10','#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_144])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_933,plain,(
    ! [B_262,C_263,A_264] :
      ( r2_hidden(k1_funct_1(B_262,C_263),A_264)
      | ~ r2_hidden(C_263,k1_relat_1(B_262))
      | ~ v1_funct_1(B_262)
      | ~ v5_relat_1(B_262,A_264)
      | ~ v1_relat_1(B_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1051,plain,(
    ! [A_266,C_267,B_268] :
      ( ~ v1_xboole_0(A_266)
      | ~ r2_hidden(C_267,k1_relat_1(B_268))
      | ~ v1_funct_1(B_268)
      | ~ v5_relat_1(B_268,A_266)
      | ~ v1_relat_1(B_268) ) ),
    inference(resolution,[status(thm)],[c_933,c_2])).

tff(c_1078,plain,(
    ! [A_269,B_270] :
      ( ~ v1_xboole_0(A_269)
      | ~ v1_funct_1(B_270)
      | ~ v5_relat_1(B_270,A_269)
      | ~ v1_relat_1(B_270)
      | v1_xboole_0(k1_relat_1(B_270)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1051])).

tff(c_1082,plain,
    ( ~ v1_xboole_0('#skF_8')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10')
    | v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_153,c_1078])).

tff(c_1086,plain,
    ( ~ v1_xboole_0('#skF_8')
    | v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_78,c_1082])).

tff(c_1087,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_406,c_1086])).

tff(c_174,plain,(
    ! [A_119,B_120,C_121] :
      ( r2_hidden('#skF_2'(A_119,B_120,C_121),B_120)
      | ~ r2_hidden(A_119,k9_relat_1(C_121,B_120))
      | ~ v1_relat_1(C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_70,plain,(
    ! [F_85] :
      ( k1_funct_1('#skF_10',F_85) != '#skF_11'
      | ~ r2_hidden(F_85,'#skF_9')
      | ~ m1_subset_1(F_85,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_188,plain,(
    ! [A_119,C_121] :
      ( k1_funct_1('#skF_10','#skF_2'(A_119,'#skF_9',C_121)) != '#skF_11'
      | ~ m1_subset_1('#skF_2'(A_119,'#skF_9',C_121),'#skF_7')
      | ~ r2_hidden(A_119,k9_relat_1(C_121,'#skF_9'))
      | ~ v1_relat_1(C_121) ) ),
    inference(resolution,[status(thm)],[c_174,c_70])).

tff(c_388,plain,
    ( k1_funct_1('#skF_10','#skF_2'('#skF_11','#skF_9','#skF_10')) != '#skF_11'
    | ~ m1_subset_1('#skF_2'('#skF_11','#skF_9','#skF_10'),'#skF_7')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_350,c_188])).

tff(c_412,plain,
    ( k1_funct_1('#skF_10','#skF_2'('#skF_11','#skF_9','#skF_10')) != '#skF_11'
    | ~ m1_subset_1('#skF_2'('#skF_11','#skF_9','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_388])).

tff(c_651,plain,(
    ~ m1_subset_1('#skF_2'('#skF_11','#skF_9','#skF_10'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_412])).

tff(c_76,plain,(
    v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_156,plain,(
    ! [A_108,B_109,C_110] :
      ( k1_relset_1(A_108,B_109,C_110) = k1_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_165,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_74,c_156])).

tff(c_1295,plain,(
    ! [B_301,A_302,C_303] :
      ( k1_xboole_0 = B_301
      | k1_relset_1(A_302,B_301,C_303) = A_302
      | ~ v1_funct_2(C_303,A_302,B_301)
      | ~ m1_subset_1(C_303,k1_zfmisc_1(k2_zfmisc_1(A_302,B_301))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1314,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_74,c_1295])).

tff(c_1321,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_165,c_1314])).

tff(c_1322,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1321])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_312,plain,(
    ! [A_161,B_162,C_163] :
      ( m1_subset_1('#skF_2'(A_161,B_162,C_163),k1_relat_1(C_163))
      | ~ r2_hidden(A_161,k9_relat_1(C_163,B_162))
      | ~ v1_relat_1(C_163) ) ),
    inference(resolution,[status(thm)],[c_298,c_8])).

tff(c_1345,plain,(
    ! [A_161,B_162] :
      ( m1_subset_1('#skF_2'(A_161,B_162,'#skF_10'),'#skF_7')
      | ~ r2_hidden(A_161,k9_relat_1('#skF_10',B_162))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1322,c_312])).

tff(c_1406,plain,(
    ! [A_307,B_308] :
      ( m1_subset_1('#skF_2'(A_307,B_308,'#skF_10'),'#skF_7')
      | ~ r2_hidden(A_307,k9_relat_1('#skF_10',B_308)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_1345])).

tff(c_1421,plain,(
    m1_subset_1('#skF_2'('#skF_11','#skF_9','#skF_10'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_350,c_1406])).

tff(c_1436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_651,c_1421])).

tff(c_1437,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1321])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    ! [A_93] :
      ( v1_xboole_0(A_93)
      | r2_hidden('#skF_1'(A_93),A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [B_67,A_66] :
      ( ~ r1_tarski(B_67,A_66)
      | ~ r2_hidden(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_109,plain,(
    ! [A_96] :
      ( ~ r1_tarski(A_96,'#skF_1'(A_96))
      | v1_xboole_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_83,c_48])).

tff(c_114,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_109])).

tff(c_1451,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1437,c_114])).

tff(c_1454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1087,c_1451])).

tff(c_1455,plain,(
    k1_funct_1('#skF_10','#skF_2'('#skF_11','#skF_9','#skF_10')) != '#skF_11' ),
    inference(splitRight,[status(thm)],[c_412])).

tff(c_419,plain,(
    ! [A_179,B_180,C_181] :
      ( r2_hidden(k4_tarski('#skF_2'(A_179,B_180,C_181),A_179),C_181)
      | ~ r2_hidden(A_179,k9_relat_1(C_181,B_180))
      | ~ v1_relat_1(C_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    ! [C_65,A_63,B_64] :
      ( k1_funct_1(C_65,A_63) = B_64
      | ~ r2_hidden(k4_tarski(A_63,B_64),C_65)
      | ~ v1_funct_1(C_65)
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4697,plain,(
    ! [C_554,A_555,B_556] :
      ( k1_funct_1(C_554,'#skF_2'(A_555,B_556,C_554)) = A_555
      | ~ v1_funct_1(C_554)
      | ~ r2_hidden(A_555,k9_relat_1(C_554,B_556))
      | ~ v1_relat_1(C_554) ) ),
    inference(resolution,[status(thm)],[c_419,c_44])).

tff(c_4725,plain,
    ( k1_funct_1('#skF_10','#skF_2'('#skF_11','#skF_9','#skF_10')) = '#skF_11'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_350,c_4697])).

tff(c_4743,plain,(
    k1_funct_1('#skF_10','#skF_2'('#skF_11','#skF_9','#skF_10')) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_78,c_4725])).

tff(c_4745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1455,c_4743])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:44:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.71/2.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.87/2.56  
% 6.87/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.87/2.56  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4
% 6.87/2.56  
% 6.87/2.56  %Foreground sorts:
% 6.87/2.56  
% 6.87/2.56  
% 6.87/2.56  %Background operators:
% 6.87/2.56  
% 6.87/2.56  
% 6.87/2.56  %Foreground operators:
% 6.87/2.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.87/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.87/2.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.87/2.56  tff('#skF_11', type, '#skF_11': $i).
% 6.87/2.56  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 6.87/2.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.87/2.56  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.87/2.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.87/2.56  tff('#skF_7', type, '#skF_7': $i).
% 6.87/2.56  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.87/2.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.87/2.56  tff('#skF_10', type, '#skF_10': $i).
% 6.87/2.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.87/2.56  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.87/2.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.87/2.56  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.87/2.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.87/2.56  tff('#skF_9', type, '#skF_9': $i).
% 6.87/2.56  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.87/2.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.87/2.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.87/2.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.87/2.56  tff('#skF_8', type, '#skF_8': $i).
% 6.87/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.87/2.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.87/2.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.87/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.87/2.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.87/2.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.87/2.56  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.87/2.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.87/2.56  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.87/2.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.87/2.56  
% 6.87/2.58  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.87/2.58  tff(f_149, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 6.87/2.58  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.87/2.58  tff(f_112, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.87/2.58  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 6.87/2.58  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.87/2.58  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.87/2.58  tff(f_83, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 6.87/2.58  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.87/2.58  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.87/2.58  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 6.87/2.58  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.87/2.58  tff(f_98, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.87/2.58  tff(f_93, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 6.87/2.58  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.87/2.58  tff(c_74, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.87/2.58  tff(c_116, plain, (![B_98, A_99]: (v1_relat_1(B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(A_99)) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.87/2.58  tff(c_123, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_74, c_116])).
% 6.87/2.58  tff(c_127, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_123])).
% 6.87/2.58  tff(c_339, plain, (![A_174, B_175, C_176, D_177]: (k7_relset_1(A_174, B_175, C_176, D_177)=k9_relat_1(C_176, D_177) | ~m1_subset_1(C_176, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.87/2.58  tff(c_346, plain, (![D_177]: (k7_relset_1('#skF_7', '#skF_8', '#skF_10', D_177)=k9_relat_1('#skF_10', D_177))), inference(resolution, [status(thm)], [c_74, c_339])).
% 6.87/2.58  tff(c_72, plain, (r2_hidden('#skF_11', k7_relset_1('#skF_7', '#skF_8', '#skF_10', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.87/2.58  tff(c_350, plain, (r2_hidden('#skF_11', k9_relat_1('#skF_10', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_346, c_72])).
% 6.87/2.58  tff(c_298, plain, (![A_161, B_162, C_163]: (r2_hidden('#skF_2'(A_161, B_162, C_163), k1_relat_1(C_163)) | ~r2_hidden(A_161, k9_relat_1(C_163, B_162)) | ~v1_relat_1(C_163))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.87/2.58  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.87/2.58  tff(c_314, plain, (![C_163, A_161, B_162]: (~v1_xboole_0(k1_relat_1(C_163)) | ~r2_hidden(A_161, k9_relat_1(C_163, B_162)) | ~v1_relat_1(C_163))), inference(resolution, [status(thm)], [c_298, c_2])).
% 6.87/2.58  tff(c_383, plain, (~v1_xboole_0(k1_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_350, c_314])).
% 6.87/2.58  tff(c_406, plain, (~v1_xboole_0(k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_383])).
% 6.87/2.58  tff(c_78, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.87/2.58  tff(c_144, plain, (![C_104, B_105, A_106]: (v5_relat_1(C_104, B_105) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_106, B_105))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.87/2.58  tff(c_153, plain, (v5_relat_1('#skF_10', '#skF_8')), inference(resolution, [status(thm)], [c_74, c_144])).
% 6.87/2.58  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.87/2.58  tff(c_933, plain, (![B_262, C_263, A_264]: (r2_hidden(k1_funct_1(B_262, C_263), A_264) | ~r2_hidden(C_263, k1_relat_1(B_262)) | ~v1_funct_1(B_262) | ~v5_relat_1(B_262, A_264) | ~v1_relat_1(B_262))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.87/2.58  tff(c_1051, plain, (![A_266, C_267, B_268]: (~v1_xboole_0(A_266) | ~r2_hidden(C_267, k1_relat_1(B_268)) | ~v1_funct_1(B_268) | ~v5_relat_1(B_268, A_266) | ~v1_relat_1(B_268))), inference(resolution, [status(thm)], [c_933, c_2])).
% 6.87/2.58  tff(c_1078, plain, (![A_269, B_270]: (~v1_xboole_0(A_269) | ~v1_funct_1(B_270) | ~v5_relat_1(B_270, A_269) | ~v1_relat_1(B_270) | v1_xboole_0(k1_relat_1(B_270)))), inference(resolution, [status(thm)], [c_4, c_1051])).
% 6.87/2.58  tff(c_1082, plain, (~v1_xboole_0('#skF_8') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | v1_xboole_0(k1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_153, c_1078])).
% 6.87/2.58  tff(c_1086, plain, (~v1_xboole_0('#skF_8') | v1_xboole_0(k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_78, c_1082])).
% 6.87/2.58  tff(c_1087, plain, (~v1_xboole_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_406, c_1086])).
% 6.87/2.58  tff(c_174, plain, (![A_119, B_120, C_121]: (r2_hidden('#skF_2'(A_119, B_120, C_121), B_120) | ~r2_hidden(A_119, k9_relat_1(C_121, B_120)) | ~v1_relat_1(C_121))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.87/2.58  tff(c_70, plain, (![F_85]: (k1_funct_1('#skF_10', F_85)!='#skF_11' | ~r2_hidden(F_85, '#skF_9') | ~m1_subset_1(F_85, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.87/2.58  tff(c_188, plain, (![A_119, C_121]: (k1_funct_1('#skF_10', '#skF_2'(A_119, '#skF_9', C_121))!='#skF_11' | ~m1_subset_1('#skF_2'(A_119, '#skF_9', C_121), '#skF_7') | ~r2_hidden(A_119, k9_relat_1(C_121, '#skF_9')) | ~v1_relat_1(C_121))), inference(resolution, [status(thm)], [c_174, c_70])).
% 6.87/2.58  tff(c_388, plain, (k1_funct_1('#skF_10', '#skF_2'('#skF_11', '#skF_9', '#skF_10'))!='#skF_11' | ~m1_subset_1('#skF_2'('#skF_11', '#skF_9', '#skF_10'), '#skF_7') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_350, c_188])).
% 6.87/2.58  tff(c_412, plain, (k1_funct_1('#skF_10', '#skF_2'('#skF_11', '#skF_9', '#skF_10'))!='#skF_11' | ~m1_subset_1('#skF_2'('#skF_11', '#skF_9', '#skF_10'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_388])).
% 6.87/2.58  tff(c_651, plain, (~m1_subset_1('#skF_2'('#skF_11', '#skF_9', '#skF_10'), '#skF_7')), inference(splitLeft, [status(thm)], [c_412])).
% 6.87/2.58  tff(c_76, plain, (v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_149])).
% 6.87/2.58  tff(c_156, plain, (![A_108, B_109, C_110]: (k1_relset_1(A_108, B_109, C_110)=k1_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.87/2.58  tff(c_165, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_74, c_156])).
% 6.87/2.58  tff(c_1295, plain, (![B_301, A_302, C_303]: (k1_xboole_0=B_301 | k1_relset_1(A_302, B_301, C_303)=A_302 | ~v1_funct_2(C_303, A_302, B_301) | ~m1_subset_1(C_303, k1_zfmisc_1(k2_zfmisc_1(A_302, B_301))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 6.87/2.58  tff(c_1314, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_74, c_1295])).
% 6.87/2.58  tff(c_1321, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_165, c_1314])).
% 6.87/2.58  tff(c_1322, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_1321])).
% 6.87/2.58  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.87/2.58  tff(c_312, plain, (![A_161, B_162, C_163]: (m1_subset_1('#skF_2'(A_161, B_162, C_163), k1_relat_1(C_163)) | ~r2_hidden(A_161, k9_relat_1(C_163, B_162)) | ~v1_relat_1(C_163))), inference(resolution, [status(thm)], [c_298, c_8])).
% 6.87/2.58  tff(c_1345, plain, (![A_161, B_162]: (m1_subset_1('#skF_2'(A_161, B_162, '#skF_10'), '#skF_7') | ~r2_hidden(A_161, k9_relat_1('#skF_10', B_162)) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1322, c_312])).
% 6.87/2.58  tff(c_1406, plain, (![A_307, B_308]: (m1_subset_1('#skF_2'(A_307, B_308, '#skF_10'), '#skF_7') | ~r2_hidden(A_307, k9_relat_1('#skF_10', B_308)))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_1345])).
% 6.87/2.58  tff(c_1421, plain, (m1_subset_1('#skF_2'('#skF_11', '#skF_9', '#skF_10'), '#skF_7')), inference(resolution, [status(thm)], [c_350, c_1406])).
% 6.87/2.58  tff(c_1436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_651, c_1421])).
% 6.87/2.58  tff(c_1437, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_1321])).
% 6.87/2.58  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.87/2.58  tff(c_83, plain, (![A_93]: (v1_xboole_0(A_93) | r2_hidden('#skF_1'(A_93), A_93))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.87/2.58  tff(c_48, plain, (![B_67, A_66]: (~r1_tarski(B_67, A_66) | ~r2_hidden(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.87/2.58  tff(c_109, plain, (![A_96]: (~r1_tarski(A_96, '#skF_1'(A_96)) | v1_xboole_0(A_96))), inference(resolution, [status(thm)], [c_83, c_48])).
% 6.87/2.58  tff(c_114, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_109])).
% 6.87/2.58  tff(c_1451, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1437, c_114])).
% 6.87/2.58  tff(c_1454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1087, c_1451])).
% 6.87/2.58  tff(c_1455, plain, (k1_funct_1('#skF_10', '#skF_2'('#skF_11', '#skF_9', '#skF_10'))!='#skF_11'), inference(splitRight, [status(thm)], [c_412])).
% 6.87/2.58  tff(c_419, plain, (![A_179, B_180, C_181]: (r2_hidden(k4_tarski('#skF_2'(A_179, B_180, C_181), A_179), C_181) | ~r2_hidden(A_179, k9_relat_1(C_181, B_180)) | ~v1_relat_1(C_181))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.87/2.58  tff(c_44, plain, (![C_65, A_63, B_64]: (k1_funct_1(C_65, A_63)=B_64 | ~r2_hidden(k4_tarski(A_63, B_64), C_65) | ~v1_funct_1(C_65) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.87/2.58  tff(c_4697, plain, (![C_554, A_555, B_556]: (k1_funct_1(C_554, '#skF_2'(A_555, B_556, C_554))=A_555 | ~v1_funct_1(C_554) | ~r2_hidden(A_555, k9_relat_1(C_554, B_556)) | ~v1_relat_1(C_554))), inference(resolution, [status(thm)], [c_419, c_44])).
% 6.87/2.58  tff(c_4725, plain, (k1_funct_1('#skF_10', '#skF_2'('#skF_11', '#skF_9', '#skF_10'))='#skF_11' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_350, c_4697])).
% 6.87/2.58  tff(c_4743, plain, (k1_funct_1('#skF_10', '#skF_2'('#skF_11', '#skF_9', '#skF_10'))='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_127, c_78, c_4725])).
% 6.87/2.58  tff(c_4745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1455, c_4743])).
% 6.87/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.87/2.58  
% 6.87/2.58  Inference rules
% 6.87/2.58  ----------------------
% 6.87/2.58  #Ref     : 0
% 6.87/2.58  #Sup     : 1007
% 6.87/2.58  #Fact    : 0
% 6.87/2.58  #Define  : 0
% 6.87/2.58  #Split   : 13
% 6.87/2.58  #Chain   : 0
% 6.87/2.58  #Close   : 0
% 6.87/2.58  
% 6.87/2.58  Ordering : KBO
% 6.87/2.58  
% 6.87/2.58  Simplification rules
% 6.87/2.58  ----------------------
% 6.87/2.58  #Subsume      : 96
% 6.87/2.58  #Demod        : 184
% 6.87/2.58  #Tautology    : 28
% 6.87/2.58  #SimpNegUnit  : 7
% 6.87/2.58  #BackRed      : 31
% 6.87/2.58  
% 6.87/2.58  #Partial instantiations: 0
% 6.87/2.58  #Strategies tried      : 1
% 6.87/2.58  
% 6.87/2.58  Timing (in seconds)
% 6.87/2.58  ----------------------
% 6.87/2.58  Preprocessing        : 0.35
% 6.87/2.58  Parsing              : 0.17
% 6.87/2.58  CNF conversion       : 0.03
% 6.87/2.58  Main loop            : 1.31
% 6.87/2.58  Inferencing          : 0.39
% 6.87/2.58  Reduction            : 0.30
% 6.87/2.58  Demodulation         : 0.21
% 6.87/2.58  BG Simplification    : 0.05
% 6.87/2.58  Subsumption          : 0.46
% 6.87/2.58  Abstraction          : 0.06
% 6.87/2.58  MUC search           : 0.00
% 6.87/2.58  Cooper               : 0.00
% 6.87/2.58  Total                : 1.69
% 6.87/2.58  Index Insertion      : 0.00
% 6.87/2.58  Index Deletion       : 0.00
% 6.87/2.58  Index Matching       : 0.00
% 6.87/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
