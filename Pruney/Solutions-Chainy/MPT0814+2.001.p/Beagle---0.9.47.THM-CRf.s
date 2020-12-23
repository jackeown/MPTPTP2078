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
% DateTime   : Thu Dec  3 10:06:51 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 224 expanded)
%              Number of leaves         :   37 (  91 expanded)
%              Depth                    :   12
%              Number of atoms          :  139 ( 490 expanded)
%              Number of equality atoms :   23 (  64 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
       => ~ ( r2_hidden(A,D)
            & ! [E,F] :
                ~ ( A = k4_tarski(E,F)
                  & r2_hidden(E,B)
                  & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ~ ( r2_hidden(D,C)
        & r1_tarski(C,k2_zfmisc_1(A,B))
        & ! [E] :
            ( m1_subset_1(E,A)
           => ! [F] :
                ( m1_subset_1(F,B)
               => D != k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_subset_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_114,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_57,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_111,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,B_55)
      | ~ m1_subset_1(A_54,k1_zfmisc_1(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_115,plain,(
    r1_tarski('#skF_9',k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_56,c_111])).

tff(c_358,plain,(
    ! [A_114,B_115,C_116,D_117] :
      ( m1_subset_1('#skF_5'(A_114,B_115,C_116,D_117),B_115)
      | ~ r1_tarski(C_116,k2_zfmisc_1(A_114,B_115))
      | ~ r2_hidden(D_117,C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_372,plain,(
    ! [D_117] :
      ( m1_subset_1('#skF_5'('#skF_7','#skF_8','#skF_9',D_117),'#skF_8')
      | ~ r2_hidden(D_117,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_115,c_358])).

tff(c_442,plain,(
    ! [A_133,B_134,C_135,D_136] :
      ( m1_subset_1('#skF_4'(A_133,B_134,C_135,D_136),A_133)
      | ~ r1_tarski(C_135,k2_zfmisc_1(A_133,B_134))
      | ~ r2_hidden(D_136,C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_456,plain,(
    ! [D_136] :
      ( m1_subset_1('#skF_4'('#skF_7','#skF_8','#skF_9',D_136),'#skF_7')
      | ~ r2_hidden(D_136,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_115,c_442])).

tff(c_26,plain,(
    ! [A_14,B_15,C_16,D_17] :
      ( k4_tarski('#skF_4'(A_14,B_15,C_16,D_17),'#skF_5'(A_14,B_15,C_16,D_17)) = D_17
      | ~ r1_tarski(C_16,k2_zfmisc_1(A_14,B_15))
      | ~ r2_hidden(D_17,C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_190,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_203,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_190])).

tff(c_233,plain,(
    ! [C_85,A_86,B_87] :
      ( v4_relat_1(C_85,A_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_248,plain,(
    v4_relat_1('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_233])).

tff(c_293,plain,(
    ! [B_101,A_102] :
      ( r1_tarski(k1_relat_1(B_101),A_102)
      | ~ v4_relat_1(B_101,A_102)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(A_27,k1_zfmisc_1(B_28))
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_159,plain,(
    ! [B_66,A_67] :
      ( v1_xboole_0(B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67))
      | ~ v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_166,plain,(
    ! [A_27,B_28] :
      ( v1_xboole_0(A_27)
      | ~ v1_xboole_0(B_28)
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(resolution,[status(thm)],[c_38,c_159])).

tff(c_419,plain,(
    ! [B_128,A_129] :
      ( v1_xboole_0(k1_relat_1(B_128))
      | ~ v1_xboole_0(A_129)
      | ~ v4_relat_1(B_128,A_129)
      | ~ v1_relat_1(B_128) ) ),
    inference(resolution,[status(thm)],[c_293,c_166])).

tff(c_425,plain,
    ( v1_xboole_0(k1_relat_1('#skF_9'))
    | ~ v1_xboole_0('#skF_7')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_248,c_419])).

tff(c_430,plain,
    ( v1_xboole_0(k1_relat_1('#skF_9'))
    | ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_425])).

tff(c_431,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_430])).

tff(c_34,plain,(
    ! [A_25,B_26] :
      ( r2_hidden(A_25,B_26)
      | v1_xboole_0(B_26)
      | ~ m1_subset_1(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_143,plain,(
    ! [A_62,B_63] :
      ( r2_hidden(A_62,B_63)
      | v1_xboole_0(B_63)
      | ~ m1_subset_1(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_52,plain,(
    ! [F_41,E_40] :
      ( ~ r2_hidden(F_41,'#skF_8')
      | ~ r2_hidden(E_40,'#skF_7')
      | k4_tarski(E_40,F_41) != '#skF_6' ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_150,plain,(
    ! [E_40,A_62] :
      ( ~ r2_hidden(E_40,'#skF_7')
      | k4_tarski(E_40,A_62) != '#skF_6'
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_62,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_143,c_52])).

tff(c_396,plain,(
    ! [E_124,A_125] :
      ( ~ r2_hidden(E_124,'#skF_7')
      | k4_tarski(E_124,A_125) != '#skF_6'
      | ~ m1_subset_1(A_125,'#skF_8') ) ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_410,plain,(
    ! [A_25,A_125] :
      ( k4_tarski(A_25,A_125) != '#skF_6'
      | ~ m1_subset_1(A_125,'#skF_8')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_25,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_34,c_396])).

tff(c_583,plain,(
    ! [A_172,A_173] :
      ( k4_tarski(A_172,A_173) != '#skF_6'
      | ~ m1_subset_1(A_173,'#skF_8')
      | ~ m1_subset_1(A_172,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_431,c_410])).

tff(c_735,plain,(
    ! [D_186,A_187,B_188,C_189] :
      ( D_186 != '#skF_6'
      | ~ m1_subset_1('#skF_5'(A_187,B_188,C_189,D_186),'#skF_8')
      | ~ m1_subset_1('#skF_4'(A_187,B_188,C_189,D_186),'#skF_7')
      | ~ r1_tarski(C_189,k2_zfmisc_1(A_187,B_188))
      | ~ r2_hidden(D_186,C_189) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_583])).

tff(c_737,plain,(
    ! [D_136] :
      ( D_136 != '#skF_6'
      | ~ m1_subset_1('#skF_5'('#skF_7','#skF_8','#skF_9',D_136),'#skF_8')
      | ~ r1_tarski('#skF_9',k2_zfmisc_1('#skF_7','#skF_8'))
      | ~ r2_hidden(D_136,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_456,c_735])).

tff(c_749,plain,(
    ! [D_191] :
      ( D_191 != '#skF_6'
      | ~ m1_subset_1('#skF_5'('#skF_7','#skF_8','#skF_9',D_191),'#skF_8')
      | ~ r2_hidden(D_191,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_737])).

tff(c_754,plain,(
    ~ r2_hidden('#skF_6','#skF_9') ),
    inference(resolution,[status(thm)],[c_372,c_749])).

tff(c_54,plain,(
    r2_hidden('#skF_6','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_754,c_54])).

tff(c_758,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_430])).

tff(c_96,plain,(
    ! [A_52] :
      ( r2_hidden('#skF_3'(A_52),A_52)
      | k1_xboole_0 = A_52 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [A_52] :
      ( ~ v1_xboole_0(A_52)
      | k1_xboole_0 = A_52 ) ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_762,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_758,c_104])).

tff(c_24,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_773,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_7',B_13) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_762,c_762,c_24])).

tff(c_80,plain,(
    ! [B_45,A_46] :
      ( ~ r2_hidden(B_45,A_46)
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_80])).

tff(c_165,plain,
    ( v1_xboole_0('#skF_9')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_56,c_159])).

tff(c_169,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_165])).

tff(c_792,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_169])).

tff(c_797,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_792])).

tff(c_798,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_802,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_798,c_104])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_812,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_802,c_802,c_22])).

tff(c_842,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_812,c_169])).

tff(c_847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_798,c_842])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:41:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.60  
% 2.74/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.60  %$ v5_relat_1 > v4_relat_1 > r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_2
% 2.74/1.60  
% 2.74/1.60  %Foreground sorts:
% 2.74/1.60  
% 2.74/1.60  
% 2.74/1.60  %Background operators:
% 2.74/1.60  
% 2.74/1.60  
% 2.74/1.60  %Foreground operators:
% 2.74/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.60  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.74/1.60  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.74/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.60  tff('#skF_7', type, '#skF_7': $i).
% 2.74/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.74/1.60  tff('#skF_6', type, '#skF_6': $i).
% 2.74/1.60  tff('#skF_9', type, '#skF_9': $i).
% 2.74/1.60  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.74/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.60  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.74/1.60  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.74/1.60  tff('#skF_8', type, '#skF_8': $i).
% 2.74/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.60  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.74/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.74/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.74/1.60  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.74/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.74/1.60  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.74/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.74/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.74/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.60  
% 2.74/1.62  tff(f_128, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_relset_1)).
% 2.74/1.62  tff(f_94, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.74/1.62  tff(f_77, axiom, (![A, B, C, D]: ~((r2_hidden(D, C) & r1_tarski(C, k2_zfmisc_1(A, B))) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => ~(D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_subset_1)).
% 2.74/1.62  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.74/1.62  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.74/1.62  tff(f_100, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.74/1.62  tff(f_84, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.74/1.62  tff(f_90, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.74/1.62  tff(f_57, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.74/1.62  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.74/1.62  tff(f_63, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.74/1.62  tff(c_56, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.74/1.62  tff(c_111, plain, (![A_54, B_55]: (r1_tarski(A_54, B_55) | ~m1_subset_1(A_54, k1_zfmisc_1(B_55)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.74/1.62  tff(c_115, plain, (r1_tarski('#skF_9', k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_56, c_111])).
% 2.74/1.62  tff(c_358, plain, (![A_114, B_115, C_116, D_117]: (m1_subset_1('#skF_5'(A_114, B_115, C_116, D_117), B_115) | ~r1_tarski(C_116, k2_zfmisc_1(A_114, B_115)) | ~r2_hidden(D_117, C_116))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.74/1.62  tff(c_372, plain, (![D_117]: (m1_subset_1('#skF_5'('#skF_7', '#skF_8', '#skF_9', D_117), '#skF_8') | ~r2_hidden(D_117, '#skF_9'))), inference(resolution, [status(thm)], [c_115, c_358])).
% 2.74/1.62  tff(c_442, plain, (![A_133, B_134, C_135, D_136]: (m1_subset_1('#skF_4'(A_133, B_134, C_135, D_136), A_133) | ~r1_tarski(C_135, k2_zfmisc_1(A_133, B_134)) | ~r2_hidden(D_136, C_135))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.74/1.62  tff(c_456, plain, (![D_136]: (m1_subset_1('#skF_4'('#skF_7', '#skF_8', '#skF_9', D_136), '#skF_7') | ~r2_hidden(D_136, '#skF_9'))), inference(resolution, [status(thm)], [c_115, c_442])).
% 2.74/1.62  tff(c_26, plain, (![A_14, B_15, C_16, D_17]: (k4_tarski('#skF_4'(A_14, B_15, C_16, D_17), '#skF_5'(A_14, B_15, C_16, D_17))=D_17 | ~r1_tarski(C_16, k2_zfmisc_1(A_14, B_15)) | ~r2_hidden(D_17, C_16))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.74/1.62  tff(c_190, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.74/1.62  tff(c_203, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_56, c_190])).
% 2.74/1.62  tff(c_233, plain, (![C_85, A_86, B_87]: (v4_relat_1(C_85, A_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.74/1.62  tff(c_248, plain, (v4_relat_1('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_56, c_233])).
% 2.74/1.62  tff(c_293, plain, (![B_101, A_102]: (r1_tarski(k1_relat_1(B_101), A_102) | ~v4_relat_1(B_101, A_102) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.74/1.62  tff(c_38, plain, (![A_27, B_28]: (m1_subset_1(A_27, k1_zfmisc_1(B_28)) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.74/1.62  tff(c_159, plain, (![B_66, A_67]: (v1_xboole_0(B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)) | ~v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.74/1.62  tff(c_166, plain, (![A_27, B_28]: (v1_xboole_0(A_27) | ~v1_xboole_0(B_28) | ~r1_tarski(A_27, B_28))), inference(resolution, [status(thm)], [c_38, c_159])).
% 2.74/1.62  tff(c_419, plain, (![B_128, A_129]: (v1_xboole_0(k1_relat_1(B_128)) | ~v1_xboole_0(A_129) | ~v4_relat_1(B_128, A_129) | ~v1_relat_1(B_128))), inference(resolution, [status(thm)], [c_293, c_166])).
% 2.74/1.62  tff(c_425, plain, (v1_xboole_0(k1_relat_1('#skF_9')) | ~v1_xboole_0('#skF_7') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_248, c_419])).
% 2.74/1.62  tff(c_430, plain, (v1_xboole_0(k1_relat_1('#skF_9')) | ~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_425])).
% 2.74/1.62  tff(c_431, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_430])).
% 2.74/1.62  tff(c_34, plain, (![A_25, B_26]: (r2_hidden(A_25, B_26) | v1_xboole_0(B_26) | ~m1_subset_1(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.74/1.62  tff(c_143, plain, (![A_62, B_63]: (r2_hidden(A_62, B_63) | v1_xboole_0(B_63) | ~m1_subset_1(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.74/1.62  tff(c_52, plain, (![F_41, E_40]: (~r2_hidden(F_41, '#skF_8') | ~r2_hidden(E_40, '#skF_7') | k4_tarski(E_40, F_41)!='#skF_6')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.74/1.62  tff(c_150, plain, (![E_40, A_62]: (~r2_hidden(E_40, '#skF_7') | k4_tarski(E_40, A_62)!='#skF_6' | v1_xboole_0('#skF_8') | ~m1_subset_1(A_62, '#skF_8'))), inference(resolution, [status(thm)], [c_143, c_52])).
% 2.74/1.62  tff(c_396, plain, (![E_124, A_125]: (~r2_hidden(E_124, '#skF_7') | k4_tarski(E_124, A_125)!='#skF_6' | ~m1_subset_1(A_125, '#skF_8'))), inference(splitLeft, [status(thm)], [c_150])).
% 2.74/1.62  tff(c_410, plain, (![A_25, A_125]: (k4_tarski(A_25, A_125)!='#skF_6' | ~m1_subset_1(A_125, '#skF_8') | v1_xboole_0('#skF_7') | ~m1_subset_1(A_25, '#skF_7'))), inference(resolution, [status(thm)], [c_34, c_396])).
% 2.74/1.62  tff(c_583, plain, (![A_172, A_173]: (k4_tarski(A_172, A_173)!='#skF_6' | ~m1_subset_1(A_173, '#skF_8') | ~m1_subset_1(A_172, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_431, c_410])).
% 2.74/1.62  tff(c_735, plain, (![D_186, A_187, B_188, C_189]: (D_186!='#skF_6' | ~m1_subset_1('#skF_5'(A_187, B_188, C_189, D_186), '#skF_8') | ~m1_subset_1('#skF_4'(A_187, B_188, C_189, D_186), '#skF_7') | ~r1_tarski(C_189, k2_zfmisc_1(A_187, B_188)) | ~r2_hidden(D_186, C_189))), inference(superposition, [status(thm), theory('equality')], [c_26, c_583])).
% 2.74/1.62  tff(c_737, plain, (![D_136]: (D_136!='#skF_6' | ~m1_subset_1('#skF_5'('#skF_7', '#skF_8', '#skF_9', D_136), '#skF_8') | ~r1_tarski('#skF_9', k2_zfmisc_1('#skF_7', '#skF_8')) | ~r2_hidden(D_136, '#skF_9'))), inference(resolution, [status(thm)], [c_456, c_735])).
% 2.74/1.62  tff(c_749, plain, (![D_191]: (D_191!='#skF_6' | ~m1_subset_1('#skF_5'('#skF_7', '#skF_8', '#skF_9', D_191), '#skF_8') | ~r2_hidden(D_191, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_737])).
% 2.74/1.62  tff(c_754, plain, (~r2_hidden('#skF_6', '#skF_9')), inference(resolution, [status(thm)], [c_372, c_749])).
% 2.74/1.62  tff(c_54, plain, (r2_hidden('#skF_6', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_128])).
% 2.74/1.62  tff(c_756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_754, c_54])).
% 2.74/1.62  tff(c_758, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_430])).
% 2.74/1.62  tff(c_96, plain, (![A_52]: (r2_hidden('#skF_3'(A_52), A_52) | k1_xboole_0=A_52)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.74/1.62  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.62  tff(c_104, plain, (![A_52]: (~v1_xboole_0(A_52) | k1_xboole_0=A_52)), inference(resolution, [status(thm)], [c_96, c_2])).
% 2.74/1.62  tff(c_762, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_758, c_104])).
% 2.74/1.62  tff(c_24, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.74/1.62  tff(c_773, plain, (![B_13]: (k2_zfmisc_1('#skF_7', B_13)='#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_762, c_762, c_24])).
% 2.74/1.62  tff(c_80, plain, (![B_45, A_46]: (~r2_hidden(B_45, A_46) | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.62  tff(c_84, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_54, c_80])).
% 2.74/1.62  tff(c_165, plain, (v1_xboole_0('#skF_9') | ~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_56, c_159])).
% 2.74/1.62  tff(c_169, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_84, c_165])).
% 2.74/1.62  tff(c_792, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_773, c_169])).
% 2.74/1.62  tff(c_797, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_758, c_792])).
% 2.74/1.62  tff(c_798, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_150])).
% 2.74/1.62  tff(c_802, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_798, c_104])).
% 2.74/1.62  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.74/1.62  tff(c_812, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_802, c_802, c_22])).
% 2.74/1.62  tff(c_842, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_812, c_169])).
% 2.74/1.62  tff(c_847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_798, c_842])).
% 2.74/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.62  
% 2.74/1.62  Inference rules
% 2.74/1.62  ----------------------
% 2.74/1.62  #Ref     : 0
% 2.74/1.62  #Sup     : 172
% 2.74/1.62  #Fact    : 0
% 2.74/1.62  #Define  : 0
% 2.74/1.62  #Split   : 6
% 2.74/1.62  #Chain   : 0
% 2.74/1.62  #Close   : 0
% 2.74/1.62  
% 2.74/1.62  Ordering : KBO
% 2.74/1.62  
% 2.74/1.62  Simplification rules
% 2.74/1.62  ----------------------
% 2.74/1.62  #Subsume      : 42
% 2.74/1.62  #Demod        : 56
% 2.74/1.62  #Tautology    : 39
% 2.74/1.62  #SimpNegUnit  : 13
% 2.74/1.62  #BackRed      : 35
% 2.74/1.62  
% 2.74/1.62  #Partial instantiations: 0
% 2.74/1.62  #Strategies tried      : 1
% 2.74/1.62  
% 2.74/1.62  Timing (in seconds)
% 2.74/1.62  ----------------------
% 2.74/1.62  Preprocessing        : 0.32
% 2.74/1.62  Parsing              : 0.16
% 2.74/1.62  CNF conversion       : 0.02
% 2.74/1.62  Main loop            : 0.39
% 2.74/1.62  Inferencing          : 0.15
% 2.74/1.62  Reduction            : 0.10
% 2.74/1.62  Demodulation         : 0.06
% 2.74/1.62  BG Simplification    : 0.02
% 2.74/1.62  Subsumption          : 0.08
% 2.74/1.62  Abstraction          : 0.01
% 2.74/1.62  MUC search           : 0.00
% 2.74/1.62  Cooper               : 0.00
% 2.74/1.62  Total                : 0.74
% 2.74/1.62  Index Insertion      : 0.00
% 2.74/1.62  Index Deletion       : 0.00
% 2.74/1.62  Index Matching       : 0.00
% 2.74/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
