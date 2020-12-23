%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:12 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 285 expanded)
%              Number of leaves         :   41 ( 117 expanded)
%              Depth                    :   12
%              Number of atoms          :  183 ( 722 expanded)
%              Number of equality atoms :   45 ( 137 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v5_relat_1(C,A)
        & v1_funct_1(C) )
     => ( r2_hidden(B,k1_relat_1(C))
       => m1_subset_1(k1_funct_1(C,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_129,axiom,(
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

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_170,plain,(
    ! [C_74,A_75,B_76] :
      ( v1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_174,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_170])).

tff(c_80,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_175,plain,(
    ! [C_77,B_78,A_79] :
      ( v5_relat_1(C_77,B_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_179,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_175])).

tff(c_46,plain,(
    ! [A_21,B_24] :
      ( k1_funct_1(A_21,B_24) = k1_xboole_0
      | r2_hidden(B_24,k1_relat_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_436,plain,(
    ! [C_132,B_133,A_134] :
      ( m1_subset_1(k1_funct_1(C_132,B_133),A_134)
      | ~ r2_hidden(B_133,k1_relat_1(C_132))
      | ~ v1_funct_1(C_132)
      | ~ v5_relat_1(C_132,A_134)
      | ~ v1_relat_1(C_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_452,plain,(
    ! [A_135,B_136,A_137] :
      ( m1_subset_1(k1_funct_1(A_135,B_136),A_137)
      | ~ v5_relat_1(A_135,A_137)
      | k1_funct_1(A_135,B_136) = k1_xboole_0
      | ~ v1_funct_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(resolution,[status(thm)],[c_46,c_436])).

tff(c_136,plain,(
    ! [A_66,B_67] :
      ( r2_hidden(A_66,B_67)
      | v1_xboole_0(B_67)
      | ~ m1_subset_1(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_72,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_143,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_136,c_72])).

tff(c_159,plain,(
    ~ m1_subset_1(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_499,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | k1_funct_1('#skF_6','#skF_4') = k1_xboole_0
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_452,c_159])).

tff(c_513,plain,(
    k1_funct_1('#skF_6','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_80,c_179,c_499])).

tff(c_514,plain,(
    ~ m1_subset_1(k1_xboole_0,'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_159])).

tff(c_42,plain,(
    ! [B_24,A_21] :
      ( r2_hidden(k4_tarski(B_24,k1_funct_1(A_21,B_24)),A_21)
      | ~ r2_hidden(B_24,k1_relat_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_522,plain,
    ( r2_hidden(k4_tarski('#skF_4',k1_xboole_0),'#skF_6')
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_42])).

tff(c_528,plain,
    ( r2_hidden(k4_tarski('#skF_4',k1_xboole_0),'#skF_6')
    | ~ r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_80,c_522])).

tff(c_536,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_528])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_78,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_261,plain,(
    ! [A_96,B_97,C_98] :
      ( k1_relset_1(A_96,B_97,C_98) = k1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_265,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_261])).

tff(c_607,plain,(
    ! [B_147,A_148,C_149] :
      ( k1_xboole_0 = B_147
      | k1_relset_1(A_148,B_147,C_149) = A_148
      | ~ v1_funct_2(C_149,A_148,B_147)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_148,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_614,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_607])).

tff(c_618,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_tarski('#skF_4') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_265,c_614])).

tff(c_619,plain,(
    k1_tarski('#skF_4') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_618])).

tff(c_30,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_113,plain,(
    ! [A_62,B_63] : k1_enumset1(A_62,A_62,B_63) = k2_tarski(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [E_11,A_5,C_7] : r2_hidden(E_11,k1_enumset1(A_5,E_11,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_146,plain,(
    ! [A_69,B_70] : r2_hidden(A_69,k2_tarski(A_69,B_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_10])).

tff(c_152,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_146])).

tff(c_638,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_619,c_152])).

tff(c_644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_536,c_638])).

tff(c_646,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_528])).

tff(c_48,plain,(
    ! [C_28,B_27,A_26] :
      ( m1_subset_1(k1_funct_1(C_28,B_27),A_26)
      | ~ r2_hidden(B_27,k1_relat_1(C_28))
      | ~ v1_funct_1(C_28)
      | ~ v5_relat_1(C_28,A_26)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_648,plain,(
    ! [A_26] :
      ( m1_subset_1(k1_funct_1('#skF_6','#skF_4'),A_26)
      | ~ v1_funct_1('#skF_6')
      | ~ v5_relat_1('#skF_6',A_26)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_646,c_48])).

tff(c_684,plain,(
    ! [A_153] :
      ( m1_subset_1(k1_xboole_0,A_153)
      | ~ v5_relat_1('#skF_6',A_153) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_80,c_513,c_648])).

tff(c_687,plain,(
    m1_subset_1(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_179,c_684])).

tff(c_691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_514,c_687])).

tff(c_692,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_732,plain,(
    ! [C_168,B_169,A_170] :
      ( v1_xboole_0(C_168)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(B_169,A_170)))
      | ~ v1_xboole_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_735,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_732])).

tff(c_738,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_735])).

tff(c_708,plain,(
    ! [C_156,A_157,B_158] :
      ( v1_relat_1(C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_712,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_708])).

tff(c_927,plain,(
    ! [B_206,A_207] :
      ( r2_hidden(k4_tarski(B_206,k1_funct_1(A_207,B_206)),A_207)
      | ~ r2_hidden(B_206,k1_relat_1(A_207))
      | ~ v1_funct_1(A_207)
      | ~ v1_relat_1(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_947,plain,(
    ! [A_208,B_209] :
      ( ~ v1_xboole_0(A_208)
      | ~ r2_hidden(B_209,k1_relat_1(A_208))
      | ~ v1_funct_1(A_208)
      | ~ v1_relat_1(A_208) ) ),
    inference(resolution,[status(thm)],[c_927,c_2])).

tff(c_992,plain,(
    ! [A_215,B_216] :
      ( ~ v1_xboole_0(A_215)
      | k1_funct_1(A_215,B_216) = k1_xboole_0
      | ~ v1_funct_1(A_215)
      | ~ v1_relat_1(A_215) ) ),
    inference(resolution,[status(thm)],[c_46,c_947])).

tff(c_996,plain,(
    ! [B_216] :
      ( k1_funct_1('#skF_6',B_216) = k1_xboole_0
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_738,c_992])).

tff(c_1008,plain,(
    ! [B_217] : k1_funct_1('#skF_6',B_217) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_80,c_996])).

tff(c_1013,plain,(
    ! [B_217] :
      ( r2_hidden(k4_tarski(B_217,k1_xboole_0),'#skF_6')
      | ~ r2_hidden(B_217,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1008,c_42])).

tff(c_1073,plain,(
    ! [B_221] :
      ( r2_hidden(k4_tarski(B_221,k1_xboole_0),'#skF_6')
      | ~ r2_hidden(B_221,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_80,c_1013])).

tff(c_1079,plain,(
    ! [B_221] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ r2_hidden(B_221,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1073,c_2])).

tff(c_1085,plain,(
    ! [B_221] : ~ r2_hidden(B_221,k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_1079])).

tff(c_744,plain,(
    ! [A_171,B_172,C_173] :
      ( k1_relset_1(A_171,B_172,C_173) = k1_relat_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_748,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_744])).

tff(c_1134,plain,(
    ! [B_226,A_227,C_228] :
      ( k1_xboole_0 = B_226
      | k1_relset_1(A_227,B_226,C_228) = A_227
      | ~ v1_funct_2(C_228,A_227,B_226)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(A_227,B_226))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1137,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_1134])).

tff(c_1140,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_tarski('#skF_4') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_748,c_1137])).

tff(c_1141,plain,(
    k1_tarski('#skF_4') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1140])).

tff(c_1158,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1141,c_152])).

tff(c_1164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1085,c_1158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:18:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.59  
% 3.28/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.60  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3
% 3.28/1.60  
% 3.28/1.60  %Foreground sorts:
% 3.28/1.60  
% 3.28/1.60  
% 3.28/1.60  %Background operators:
% 3.28/1.60  
% 3.28/1.60  
% 3.28/1.60  %Foreground operators:
% 3.28/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.28/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.28/1.60  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.28/1.60  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.28/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.28/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.28/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.28/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.28/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.28/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.28/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.28/1.60  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.28/1.60  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.28/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.60  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.28/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.28/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.60  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.28/1.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.28/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.28/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.28/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.60  
% 3.28/1.61  tff(f_141, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 3.28/1.61  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.28/1.61  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.28/1.61  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_funct_1)).
% 3.28/1.61  tff(f_90, axiom, (![A, B, C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (r2_hidden(B, k1_relat_1(C)) => m1_subset_1(k1_funct_1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_funct_1)).
% 3.28/1.61  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.28/1.61  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.28/1.61  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.28/1.61  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.28/1.61  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.28/1.61  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.28/1.61  tff(f_107, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.28/1.61  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.28/1.61  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.28/1.61  tff(c_170, plain, (![C_74, A_75, B_76]: (v1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.28/1.61  tff(c_174, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_170])).
% 3.28/1.61  tff(c_80, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.28/1.61  tff(c_175, plain, (![C_77, B_78, A_79]: (v5_relat_1(C_77, B_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.28/1.61  tff(c_179, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_175])).
% 3.28/1.61  tff(c_46, plain, (![A_21, B_24]: (k1_funct_1(A_21, B_24)=k1_xboole_0 | r2_hidden(B_24, k1_relat_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.28/1.61  tff(c_436, plain, (![C_132, B_133, A_134]: (m1_subset_1(k1_funct_1(C_132, B_133), A_134) | ~r2_hidden(B_133, k1_relat_1(C_132)) | ~v1_funct_1(C_132) | ~v5_relat_1(C_132, A_134) | ~v1_relat_1(C_132))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.28/1.61  tff(c_452, plain, (![A_135, B_136, A_137]: (m1_subset_1(k1_funct_1(A_135, B_136), A_137) | ~v5_relat_1(A_135, A_137) | k1_funct_1(A_135, B_136)=k1_xboole_0 | ~v1_funct_1(A_135) | ~v1_relat_1(A_135))), inference(resolution, [status(thm)], [c_46, c_436])).
% 3.28/1.61  tff(c_136, plain, (![A_66, B_67]: (r2_hidden(A_66, B_67) | v1_xboole_0(B_67) | ~m1_subset_1(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.28/1.61  tff(c_72, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.28/1.61  tff(c_143, plain, (v1_xboole_0('#skF_5') | ~m1_subset_1(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_136, c_72])).
% 3.28/1.61  tff(c_159, plain, (~m1_subset_1(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_143])).
% 3.28/1.61  tff(c_499, plain, (~v5_relat_1('#skF_6', '#skF_5') | k1_funct_1('#skF_6', '#skF_4')=k1_xboole_0 | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_452, c_159])).
% 3.28/1.61  tff(c_513, plain, (k1_funct_1('#skF_6', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_174, c_80, c_179, c_499])).
% 3.28/1.61  tff(c_514, plain, (~m1_subset_1(k1_xboole_0, '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_513, c_159])).
% 3.28/1.61  tff(c_42, plain, (![B_24, A_21]: (r2_hidden(k4_tarski(B_24, k1_funct_1(A_21, B_24)), A_21) | ~r2_hidden(B_24, k1_relat_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.28/1.61  tff(c_522, plain, (r2_hidden(k4_tarski('#skF_4', k1_xboole_0), '#skF_6') | ~r2_hidden('#skF_4', k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_513, c_42])).
% 3.28/1.61  tff(c_528, plain, (r2_hidden(k4_tarski('#skF_4', k1_xboole_0), '#skF_6') | ~r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_80, c_522])).
% 3.28/1.61  tff(c_536, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_528])).
% 3.28/1.61  tff(c_74, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.28/1.61  tff(c_78, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.28/1.61  tff(c_261, plain, (![A_96, B_97, C_98]: (k1_relset_1(A_96, B_97, C_98)=k1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.28/1.61  tff(c_265, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_261])).
% 3.28/1.61  tff(c_607, plain, (![B_147, A_148, C_149]: (k1_xboole_0=B_147 | k1_relset_1(A_148, B_147, C_149)=A_148 | ~v1_funct_2(C_149, A_148, B_147) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_148, B_147))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.28/1.61  tff(c_614, plain, (k1_xboole_0='#skF_5' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4') | ~v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_76, c_607])).
% 3.28/1.61  tff(c_618, plain, (k1_xboole_0='#skF_5' | k1_tarski('#skF_4')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_265, c_614])).
% 3.28/1.61  tff(c_619, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_74, c_618])).
% 3.28/1.61  tff(c_30, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.28/1.61  tff(c_113, plain, (![A_62, B_63]: (k1_enumset1(A_62, A_62, B_63)=k2_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.28/1.61  tff(c_10, plain, (![E_11, A_5, C_7]: (r2_hidden(E_11, k1_enumset1(A_5, E_11, C_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.28/1.61  tff(c_146, plain, (![A_69, B_70]: (r2_hidden(A_69, k2_tarski(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_10])).
% 3.28/1.61  tff(c_152, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_146])).
% 3.28/1.61  tff(c_638, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_619, c_152])).
% 3.28/1.61  tff(c_644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_536, c_638])).
% 3.28/1.61  tff(c_646, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_528])).
% 3.28/1.61  tff(c_48, plain, (![C_28, B_27, A_26]: (m1_subset_1(k1_funct_1(C_28, B_27), A_26) | ~r2_hidden(B_27, k1_relat_1(C_28)) | ~v1_funct_1(C_28) | ~v5_relat_1(C_28, A_26) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.28/1.61  tff(c_648, plain, (![A_26]: (m1_subset_1(k1_funct_1('#skF_6', '#skF_4'), A_26) | ~v1_funct_1('#skF_6') | ~v5_relat_1('#skF_6', A_26) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_646, c_48])).
% 3.28/1.61  tff(c_684, plain, (![A_153]: (m1_subset_1(k1_xboole_0, A_153) | ~v5_relat_1('#skF_6', A_153))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_80, c_513, c_648])).
% 3.28/1.61  tff(c_687, plain, (m1_subset_1(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_179, c_684])).
% 3.28/1.61  tff(c_691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_514, c_687])).
% 3.28/1.61  tff(c_692, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_143])).
% 3.28/1.61  tff(c_732, plain, (![C_168, B_169, A_170]: (v1_xboole_0(C_168) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(B_169, A_170))) | ~v1_xboole_0(A_170))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.28/1.61  tff(c_735, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_76, c_732])).
% 3.28/1.61  tff(c_738, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_692, c_735])).
% 3.28/1.61  tff(c_708, plain, (![C_156, A_157, B_158]: (v1_relat_1(C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.28/1.61  tff(c_712, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_708])).
% 3.28/1.61  tff(c_927, plain, (![B_206, A_207]: (r2_hidden(k4_tarski(B_206, k1_funct_1(A_207, B_206)), A_207) | ~r2_hidden(B_206, k1_relat_1(A_207)) | ~v1_funct_1(A_207) | ~v1_relat_1(A_207))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.28/1.61  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.28/1.61  tff(c_947, plain, (![A_208, B_209]: (~v1_xboole_0(A_208) | ~r2_hidden(B_209, k1_relat_1(A_208)) | ~v1_funct_1(A_208) | ~v1_relat_1(A_208))), inference(resolution, [status(thm)], [c_927, c_2])).
% 3.28/1.61  tff(c_992, plain, (![A_215, B_216]: (~v1_xboole_0(A_215) | k1_funct_1(A_215, B_216)=k1_xboole_0 | ~v1_funct_1(A_215) | ~v1_relat_1(A_215))), inference(resolution, [status(thm)], [c_46, c_947])).
% 3.28/1.61  tff(c_996, plain, (![B_216]: (k1_funct_1('#skF_6', B_216)=k1_xboole_0 | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_738, c_992])).
% 3.28/1.61  tff(c_1008, plain, (![B_217]: (k1_funct_1('#skF_6', B_217)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_712, c_80, c_996])).
% 3.28/1.61  tff(c_1013, plain, (![B_217]: (r2_hidden(k4_tarski(B_217, k1_xboole_0), '#skF_6') | ~r2_hidden(B_217, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1008, c_42])).
% 3.28/1.61  tff(c_1073, plain, (![B_221]: (r2_hidden(k4_tarski(B_221, k1_xboole_0), '#skF_6') | ~r2_hidden(B_221, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_712, c_80, c_1013])).
% 3.28/1.61  tff(c_1079, plain, (![B_221]: (~v1_xboole_0('#skF_6') | ~r2_hidden(B_221, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_1073, c_2])).
% 3.28/1.61  tff(c_1085, plain, (![B_221]: (~r2_hidden(B_221, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_738, c_1079])).
% 3.28/1.61  tff(c_744, plain, (![A_171, B_172, C_173]: (k1_relset_1(A_171, B_172, C_173)=k1_relat_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.28/1.61  tff(c_748, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_744])).
% 3.28/1.61  tff(c_1134, plain, (![B_226, A_227, C_228]: (k1_xboole_0=B_226 | k1_relset_1(A_227, B_226, C_228)=A_227 | ~v1_funct_2(C_228, A_227, B_226) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(A_227, B_226))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.28/1.61  tff(c_1137, plain, (k1_xboole_0='#skF_5' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4') | ~v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_76, c_1134])).
% 3.28/1.61  tff(c_1140, plain, (k1_xboole_0='#skF_5' | k1_tarski('#skF_4')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_748, c_1137])).
% 3.28/1.61  tff(c_1141, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_74, c_1140])).
% 3.28/1.61  tff(c_1158, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1141, c_152])).
% 3.28/1.61  tff(c_1164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1085, c_1158])).
% 3.28/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.61  
% 3.28/1.61  Inference rules
% 3.28/1.61  ----------------------
% 3.28/1.61  #Ref     : 0
% 3.28/1.61  #Sup     : 217
% 3.28/1.61  #Fact    : 4
% 3.28/1.61  #Define  : 0
% 3.28/1.61  #Split   : 6
% 3.28/1.61  #Chain   : 0
% 3.28/1.61  #Close   : 0
% 3.28/1.61  
% 3.28/1.61  Ordering : KBO
% 3.28/1.61  
% 3.28/1.61  Simplification rules
% 3.28/1.61  ----------------------
% 3.28/1.61  #Subsume      : 28
% 3.28/1.61  #Demod        : 92
% 3.28/1.61  #Tautology    : 75
% 3.28/1.61  #SimpNegUnit  : 27
% 3.28/1.61  #BackRed      : 12
% 3.28/1.61  
% 3.28/1.61  #Partial instantiations: 0
% 3.28/1.61  #Strategies tried      : 1
% 3.28/1.61  
% 3.28/1.61  Timing (in seconds)
% 3.28/1.61  ----------------------
% 3.28/1.62  Preprocessing        : 0.42
% 3.28/1.62  Parsing              : 0.22
% 3.28/1.62  CNF conversion       : 0.03
% 3.28/1.62  Main loop            : 0.43
% 3.28/1.62  Inferencing          : 0.16
% 3.28/1.62  Reduction            : 0.13
% 3.28/1.62  Demodulation         : 0.09
% 3.28/1.62  BG Simplification    : 0.03
% 3.28/1.62  Subsumption          : 0.07
% 3.28/1.62  Abstraction          : 0.02
% 3.28/1.62  MUC search           : 0.00
% 3.28/1.62  Cooper               : 0.00
% 3.28/1.62  Total                : 0.88
% 3.28/1.62  Index Insertion      : 0.00
% 3.28/1.62  Index Deletion       : 0.00
% 3.28/1.62  Index Matching       : 0.00
% 3.28/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
