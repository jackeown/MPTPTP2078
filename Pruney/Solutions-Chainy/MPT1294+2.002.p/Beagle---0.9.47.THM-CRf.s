%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:38 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 129 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :  109 ( 261 expanded)
%              Number of equality atoms :   25 ( 132 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_setfam_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( ~ ( B != k1_xboole_0
              & k7_setfam_1(A,B) = k1_xboole_0 )
          & ~ ( k7_setfam_1(A,B) != k1_xboole_0
              & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tops_2)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
          <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_36,plain,
    ( k1_xboole_0 != '#skF_3'
    | k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_70,plain,(
    k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_30,plain,
    ( k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_86,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_30])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_93,plain,(
    ! [A_10] : m1_subset_1('#skF_3',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_16])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k7_setfam_1(A_11,B_12),k1_zfmisc_1(k1_zfmisc_1(A_11)))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(k1_zfmisc_1(A_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_169,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(k7_setfam_1(A_45,B_46),k1_zfmisc_1(k1_zfmisc_1(A_45)))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k1_zfmisc_1(A_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26,plain,(
    ! [A_19,C_21,B_20] :
      ( m1_subset_1(A_19,C_21)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(C_21))
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_180,plain,(
    ! [A_47,A_48,B_49] :
      ( m1_subset_1(A_47,k1_zfmisc_1(A_48))
      | ~ r2_hidden(A_47,k7_setfam_1(A_48,B_49))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(resolution,[status(thm)],[c_169,c_26])).

tff(c_186,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1('#skF_1'(k7_setfam_1(A_48,B_49)),k1_zfmisc_1(A_48))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(A_48)))
      | v1_xboole_0(k7_setfam_1(A_48,B_49)) ) ),
    inference(resolution,[status(thm)],[c_4,c_180])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_62,plain,(
    ! [A_28,B_29] : ~ r2_hidden(A_28,k2_zfmisc_1(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_65,plain,(
    ! [A_6] : ~ r2_hidden(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_62])).

tff(c_89,plain,(
    ! [A_6] : ~ r2_hidden(A_6,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_65])).

tff(c_157,plain,(
    ! [A_42,B_43] :
      ( k7_setfam_1(A_42,k7_setfam_1(A_42,B_43)) = B_43
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(A_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_161,plain,(
    ! [A_42] : k7_setfam_1(A_42,k7_setfam_1(A_42,'#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_93,c_157])).

tff(c_226,plain,(
    ! [A_60,C_61,B_62] :
      ( r2_hidden(k3_subset_1(A_60,C_61),k7_setfam_1(A_60,B_62))
      | ~ r2_hidden(C_61,B_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_237,plain,(
    ! [A_42,C_61] :
      ( r2_hidden(k3_subset_1(A_42,C_61),'#skF_3')
      | ~ r2_hidden(C_61,k7_setfam_1(A_42,'#skF_3'))
      | ~ m1_subset_1(C_61,k1_zfmisc_1(A_42))
      | ~ m1_subset_1(k7_setfam_1(A_42,'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(A_42))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_226])).

tff(c_254,plain,(
    ! [C_68,A_69] :
      ( ~ r2_hidden(C_68,k7_setfam_1(A_69,'#skF_3'))
      | ~ m1_subset_1(C_68,k1_zfmisc_1(A_69))
      | ~ m1_subset_1(k7_setfam_1(A_69,'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(A_69))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_237])).

tff(c_272,plain,(
    ! [A_73] :
      ( ~ m1_subset_1('#skF_1'(k7_setfam_1(A_73,'#skF_3')),k1_zfmisc_1(A_73))
      | ~ m1_subset_1(k7_setfam_1(A_73,'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(A_73)))
      | v1_xboole_0(k7_setfam_1(A_73,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_4,c_254])).

tff(c_276,plain,(
    ! [A_48] :
      ( ~ m1_subset_1(k7_setfam_1(A_48,'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(A_48)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_48)))
      | v1_xboole_0(k7_setfam_1(A_48,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_186,c_272])).

tff(c_280,plain,(
    ! [A_74] :
      ( ~ m1_subset_1(k7_setfam_1(A_74,'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(A_74)))
      | v1_xboole_0(k7_setfam_1(A_74,'#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_276])).

tff(c_284,plain,(
    ! [A_11] :
      ( v1_xboole_0(k7_setfam_1(A_11,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_11))) ) ),
    inference(resolution,[status(thm)],[c_18,c_280])).

tff(c_289,plain,(
    ! [A_75] : v1_xboole_0(k7_setfam_1(A_75,'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_284])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_90,plain,(
    ! [A_5] :
      ( A_5 = '#skF_3'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_6])).

tff(c_293,plain,(
    ! [A_75] : k7_setfam_1(A_75,'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_289,c_90])).

tff(c_88,plain,(
    k7_setfam_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_70])).

tff(c_361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_88])).

tff(c_362,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_396,plain,(
    ! [A_81,C_82,B_83] :
      ( m1_subset_1(A_81,C_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(C_82))
      | ~ r2_hidden(A_81,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_401,plain,(
    ! [A_81] :
      ( m1_subset_1(A_81,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_81,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_396])).

tff(c_363,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_457,plain,(
    ! [A_93,C_94,B_95] :
      ( r2_hidden(k3_subset_1(A_93,C_94),k7_setfam_1(A_93,B_95))
      | ~ r2_hidden(C_94,B_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(A_93))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k1_zfmisc_1(A_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_471,plain,(
    ! [C_94] :
      ( r2_hidden(k3_subset_1('#skF_2',C_94),k1_xboole_0)
      | ~ r2_hidden(C_94,'#skF_3')
      | ~ m1_subset_1(C_94,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_457])).

tff(c_478,plain,(
    ! [C_94] :
      ( r2_hidden(k3_subset_1('#skF_2',C_94),k1_xboole_0)
      | ~ r2_hidden(C_94,'#skF_3')
      | ~ m1_subset_1(C_94,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_471])).

tff(c_480,plain,(
    ! [C_96] :
      ( ~ r2_hidden(C_96,'#skF_3')
      | ~ m1_subset_1(C_96,k1_zfmisc_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_478])).

tff(c_490,plain,(
    ! [A_97] : ~ r2_hidden(A_97,'#skF_3') ),
    inference(resolution,[status(thm)],[c_401,c_480])).

tff(c_495,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_490])).

tff(c_498,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_495,c_6])).

tff(c_502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_362,c_498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.31  
% 2.13/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.31  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_setfam_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.13/1.31  
% 2.13/1.31  %Foreground sorts:
% 2.13/1.31  
% 2.13/1.31  
% 2.13/1.31  %Background operators:
% 2.13/1.31  
% 2.13/1.31  
% 2.13/1.31  %Foreground operators:
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.13/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.31  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.13/1.31  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.13/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.13/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.13/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.31  
% 2.13/1.32  tff(f_84, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)) & ~(~(k7_setfam_1(A, B) = k1_xboole_0) & (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tops_2)).
% 2.13/1.32  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.13/1.32  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 2.13/1.32  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.13/1.32  tff(f_69, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.13/1.32  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.13/1.32  tff(f_44, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.13/1.32  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.13/1.32  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_setfam_1)).
% 2.13/1.32  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.13/1.32  tff(c_36, plain, (k1_xboole_0!='#skF_3' | k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.13/1.32  tff(c_70, plain, (k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 2.13/1.32  tff(c_30, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.13/1.32  tff(c_86, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_70, c_30])).
% 2.13/1.32  tff(c_16, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.13/1.32  tff(c_93, plain, (![A_10]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_16])).
% 2.13/1.32  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(k7_setfam_1(A_11, B_12), k1_zfmisc_1(k1_zfmisc_1(A_11))) | ~m1_subset_1(B_12, k1_zfmisc_1(k1_zfmisc_1(A_11))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.32  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.32  tff(c_169, plain, (![A_45, B_46]: (m1_subset_1(k7_setfam_1(A_45, B_46), k1_zfmisc_1(k1_zfmisc_1(A_45))) | ~m1_subset_1(B_46, k1_zfmisc_1(k1_zfmisc_1(A_45))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.32  tff(c_26, plain, (![A_19, C_21, B_20]: (m1_subset_1(A_19, C_21) | ~m1_subset_1(B_20, k1_zfmisc_1(C_21)) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.13/1.32  tff(c_180, plain, (![A_47, A_48, B_49]: (m1_subset_1(A_47, k1_zfmisc_1(A_48)) | ~r2_hidden(A_47, k7_setfam_1(A_48, B_49)) | ~m1_subset_1(B_49, k1_zfmisc_1(k1_zfmisc_1(A_48))))), inference(resolution, [status(thm)], [c_169, c_26])).
% 2.13/1.32  tff(c_186, plain, (![A_48, B_49]: (m1_subset_1('#skF_1'(k7_setfam_1(A_48, B_49)), k1_zfmisc_1(A_48)) | ~m1_subset_1(B_49, k1_zfmisc_1(k1_zfmisc_1(A_48))) | v1_xboole_0(k7_setfam_1(A_48, B_49)))), inference(resolution, [status(thm)], [c_4, c_180])).
% 2.13/1.32  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.13/1.32  tff(c_62, plain, (![A_28, B_29]: (~r2_hidden(A_28, k2_zfmisc_1(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.13/1.32  tff(c_65, plain, (![A_6]: (~r2_hidden(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_62])).
% 2.13/1.32  tff(c_89, plain, (![A_6]: (~r2_hidden(A_6, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_65])).
% 2.13/1.32  tff(c_157, plain, (![A_42, B_43]: (k7_setfam_1(A_42, k7_setfam_1(A_42, B_43))=B_43 | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(A_42))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.13/1.32  tff(c_161, plain, (![A_42]: (k7_setfam_1(A_42, k7_setfam_1(A_42, '#skF_3'))='#skF_3')), inference(resolution, [status(thm)], [c_93, c_157])).
% 2.13/1.32  tff(c_226, plain, (![A_60, C_61, B_62]: (r2_hidden(k3_subset_1(A_60, C_61), k7_setfam_1(A_60, B_62)) | ~r2_hidden(C_61, B_62) | ~m1_subset_1(C_61, k1_zfmisc_1(A_60)) | ~m1_subset_1(B_62, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.13/1.32  tff(c_237, plain, (![A_42, C_61]: (r2_hidden(k3_subset_1(A_42, C_61), '#skF_3') | ~r2_hidden(C_61, k7_setfam_1(A_42, '#skF_3')) | ~m1_subset_1(C_61, k1_zfmisc_1(A_42)) | ~m1_subset_1(k7_setfam_1(A_42, '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(A_42))))), inference(superposition, [status(thm), theory('equality')], [c_161, c_226])).
% 2.13/1.32  tff(c_254, plain, (![C_68, A_69]: (~r2_hidden(C_68, k7_setfam_1(A_69, '#skF_3')) | ~m1_subset_1(C_68, k1_zfmisc_1(A_69)) | ~m1_subset_1(k7_setfam_1(A_69, '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(A_69))))), inference(negUnitSimplification, [status(thm)], [c_89, c_237])).
% 2.13/1.32  tff(c_272, plain, (![A_73]: (~m1_subset_1('#skF_1'(k7_setfam_1(A_73, '#skF_3')), k1_zfmisc_1(A_73)) | ~m1_subset_1(k7_setfam_1(A_73, '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(A_73))) | v1_xboole_0(k7_setfam_1(A_73, '#skF_3')))), inference(resolution, [status(thm)], [c_4, c_254])).
% 2.13/1.32  tff(c_276, plain, (![A_48]: (~m1_subset_1(k7_setfam_1(A_48, '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(A_48))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_48))) | v1_xboole_0(k7_setfam_1(A_48, '#skF_3')))), inference(resolution, [status(thm)], [c_186, c_272])).
% 2.13/1.32  tff(c_280, plain, (![A_74]: (~m1_subset_1(k7_setfam_1(A_74, '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(A_74))) | v1_xboole_0(k7_setfam_1(A_74, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_276])).
% 2.13/1.32  tff(c_284, plain, (![A_11]: (v1_xboole_0(k7_setfam_1(A_11, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_11))))), inference(resolution, [status(thm)], [c_18, c_280])).
% 2.13/1.32  tff(c_289, plain, (![A_75]: (v1_xboole_0(k7_setfam_1(A_75, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_284])).
% 2.13/1.32  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.32  tff(c_90, plain, (![A_5]: (A_5='#skF_3' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_6])).
% 2.13/1.32  tff(c_293, plain, (![A_75]: (k7_setfam_1(A_75, '#skF_3')='#skF_3')), inference(resolution, [status(thm)], [c_289, c_90])).
% 2.13/1.32  tff(c_88, plain, (k7_setfam_1('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_70])).
% 2.13/1.32  tff(c_361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_293, c_88])).
% 2.13/1.32  tff(c_362, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 2.13/1.32  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.13/1.32  tff(c_396, plain, (![A_81, C_82, B_83]: (m1_subset_1(A_81, C_82) | ~m1_subset_1(B_83, k1_zfmisc_1(C_82)) | ~r2_hidden(A_81, B_83))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.13/1.32  tff(c_401, plain, (![A_81]: (m1_subset_1(A_81, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_81, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_396])).
% 2.13/1.32  tff(c_363, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.13/1.32  tff(c_457, plain, (![A_93, C_94, B_95]: (r2_hidden(k3_subset_1(A_93, C_94), k7_setfam_1(A_93, B_95)) | ~r2_hidden(C_94, B_95) | ~m1_subset_1(C_94, k1_zfmisc_1(A_93)) | ~m1_subset_1(B_95, k1_zfmisc_1(k1_zfmisc_1(A_93))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.13/1.32  tff(c_471, plain, (![C_94]: (r2_hidden(k3_subset_1('#skF_2', C_94), k1_xboole_0) | ~r2_hidden(C_94, '#skF_3') | ~m1_subset_1(C_94, k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_363, c_457])).
% 2.13/1.32  tff(c_478, plain, (![C_94]: (r2_hidden(k3_subset_1('#skF_2', C_94), k1_xboole_0) | ~r2_hidden(C_94, '#skF_3') | ~m1_subset_1(C_94, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_471])).
% 2.13/1.32  tff(c_480, plain, (![C_96]: (~r2_hidden(C_96, '#skF_3') | ~m1_subset_1(C_96, k1_zfmisc_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_65, c_478])).
% 2.13/1.32  tff(c_490, plain, (![A_97]: (~r2_hidden(A_97, '#skF_3'))), inference(resolution, [status(thm)], [c_401, c_480])).
% 2.13/1.32  tff(c_495, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_490])).
% 2.13/1.32  tff(c_498, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_495, c_6])).
% 2.13/1.32  tff(c_502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_362, c_498])).
% 2.13/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.32  
% 2.13/1.32  Inference rules
% 2.13/1.32  ----------------------
% 2.13/1.32  #Ref     : 0
% 2.13/1.32  #Sup     : 105
% 2.13/1.32  #Fact    : 0
% 2.13/1.32  #Define  : 0
% 2.13/1.32  #Split   : 1
% 2.13/1.32  #Chain   : 0
% 2.13/1.32  #Close   : 0
% 2.13/1.32  
% 2.13/1.32  Ordering : KBO
% 2.13/1.32  
% 2.13/1.32  Simplification rules
% 2.13/1.32  ----------------------
% 2.13/1.32  #Subsume      : 15
% 2.13/1.32  #Demod        : 47
% 2.13/1.32  #Tautology    : 58
% 2.13/1.32  #SimpNegUnit  : 6
% 2.13/1.32  #BackRed      : 10
% 2.13/1.32  
% 2.13/1.32  #Partial instantiations: 0
% 2.13/1.32  #Strategies tried      : 1
% 2.13/1.32  
% 2.13/1.32  Timing (in seconds)
% 2.13/1.32  ----------------------
% 2.56/1.33  Preprocessing        : 0.29
% 2.56/1.33  Parsing              : 0.16
% 2.56/1.33  CNF conversion       : 0.02
% 2.56/1.33  Main loop            : 0.27
% 2.56/1.33  Inferencing          : 0.10
% 2.56/1.33  Reduction            : 0.08
% 2.56/1.33  Demodulation         : 0.05
% 2.56/1.33  BG Simplification    : 0.01
% 2.56/1.33  Subsumption          : 0.05
% 2.56/1.33  Abstraction          : 0.01
% 2.56/1.33  MUC search           : 0.00
% 2.56/1.33  Cooper               : 0.00
% 2.56/1.33  Total                : 0.60
% 2.56/1.33  Index Insertion      : 0.00
% 2.56/1.33  Index Deletion       : 0.00
% 2.56/1.33  Index Matching       : 0.00
% 2.56/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
