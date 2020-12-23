%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:50 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 101 expanded)
%              Number of leaves         :   17 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 229 expanded)
%              Number of equality atoms :    6 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
            <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k3_subset_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_33,plain,(
    ~ r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_32,plain,
    ( r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3'))
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_41,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_32])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k7_setfam_1(A_16,B_17),k1_zfmisc_1(k1_zfmisc_1(A_16)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( k3_subset_1(A_19,k3_subset_1(A_19,B_20)) = B_20
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_34])).

tff(c_138,plain,(
    ! [A_32,D_33,B_34] :
      ( r2_hidden(k3_subset_1(A_32,D_33),B_34)
      | ~ r2_hidden(D_33,k7_setfam_1(A_32,B_34))
      | ~ m1_subset_1(D_33,k1_zfmisc_1(A_32))
      | ~ m1_subset_1(k7_setfam_1(A_32,B_34),k1_zfmisc_1(k1_zfmisc_1(A_32)))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k1_zfmisc_1(A_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_142,plain,(
    ! [A_35,D_36,B_37] :
      ( r2_hidden(k3_subset_1(A_35,D_36),B_37)
      | ~ r2_hidden(D_36,k7_setfam_1(A_35,B_37))
      | ~ m1_subset_1(D_36,k1_zfmisc_1(A_35))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(A_35))) ) ),
    inference(resolution,[status(thm)],[c_20,c_138])).

tff(c_180,plain,(
    ! [A_42,D_43,B_44] :
      ( r2_hidden(k3_subset_1(A_42,D_43),k7_setfam_1(A_42,B_44))
      | ~ r2_hidden(D_43,k7_setfam_1(A_42,k7_setfam_1(A_42,B_44)))
      | ~ m1_subset_1(D_43,k1_zfmisc_1(A_42))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k1_zfmisc_1(A_42))) ) ),
    inference(resolution,[status(thm)],[c_20,c_142])).

tff(c_197,plain,(
    ! [B_44] :
      ( r2_hidden('#skF_4',k7_setfam_1('#skF_2',B_44))
      | ~ r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2',k7_setfam_1('#skF_2',B_44)))
      | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_180])).

tff(c_202,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_205,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2,c_202])).

tff(c_209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_205])).

tff(c_211,plain,(
    m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_157,plain,(
    ! [D_38,A_39,B_40] :
      ( r2_hidden(D_38,k7_setfam_1(A_39,B_40))
      | ~ r2_hidden(k3_subset_1(A_39,D_38),B_40)
      | ~ m1_subset_1(D_38,k1_zfmisc_1(A_39))
      | ~ m1_subset_1(k7_setfam_1(A_39,B_40),k1_zfmisc_1(k1_zfmisc_1(A_39)))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k1_zfmisc_1(A_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_165,plain,(
    ! [B_40] :
      ( r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2',B_40))
      | ~ r2_hidden('#skF_4',B_40)
      | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(k7_setfam_1('#skF_2',B_40),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_157])).

tff(c_476,plain,(
    ! [B_66] :
      ( r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2',B_66))
      | ~ r2_hidden('#skF_4',B_66)
      | ~ m1_subset_1(k7_setfam_1('#skF_2',B_66),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_165])).

tff(c_482,plain,(
    ! [B_67] :
      ( r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2',B_67))
      | ~ r2_hidden('#skF_4',B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_20,c_476])).

tff(c_493,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_482,c_33])).

tff(c_502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_41,c_493])).

tff(c_503,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_504,plain,(
    r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_505,plain,(
    ! [A_68,B_69] :
      ( k3_subset_1(A_68,k3_subset_1(A_68,B_69)) = B_69
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_511,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22,c_505])).

tff(c_610,plain,(
    ! [A_81,D_82,B_83] :
      ( r2_hidden(k3_subset_1(A_81,D_82),B_83)
      | ~ r2_hidden(D_82,k7_setfam_1(A_81,B_83))
      | ~ m1_subset_1(D_82,k1_zfmisc_1(A_81))
      | ~ m1_subset_1(k7_setfam_1(A_81,B_83),k1_zfmisc_1(k1_zfmisc_1(A_81)))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k1_zfmisc_1(A_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_614,plain,(
    ! [A_84,D_85,B_86] :
      ( r2_hidden(k3_subset_1(A_84,D_85),B_86)
      | ~ r2_hidden(D_85,k7_setfam_1(A_84,B_86))
      | ~ m1_subset_1(D_85,k1_zfmisc_1(A_84))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k1_zfmisc_1(A_84))) ) ),
    inference(resolution,[status(thm)],[c_20,c_610])).

tff(c_643,plain,(
    ! [D_90] :
      ( r2_hidden(k3_subset_1('#skF_2',D_90),'#skF_3')
      | ~ r2_hidden(D_90,k7_setfam_1('#skF_2','#skF_3'))
      | ~ m1_subset_1(D_90,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_24,c_614])).

tff(c_652,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | ~ r2_hidden(k3_subset_1('#skF_2','#skF_4'),k7_setfam_1('#skF_2','#skF_3'))
    | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_643])).

tff(c_657,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_652])).

tff(c_658,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_2','#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_503,c_657])).

tff(c_661,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2,c_658])).

tff(c_665,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_661])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:10:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.39  
% 2.60/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.39  %$ r2_hidden > m1_subset_1 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.60/1.39  
% 2.60/1.39  %Foreground sorts:
% 2.60/1.39  
% 2.60/1.39  
% 2.60/1.39  %Background operators:
% 2.60/1.39  
% 2.60/1.39  
% 2.60/1.39  %Foreground operators:
% 2.60/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.60/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.39  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.60/1.39  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.60/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.60/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.60/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.60/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.60/1.39  
% 2.86/1.40  tff(f_61, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_setfam_1)).
% 2.86/1.40  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.86/1.40  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 2.86/1.40  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.86/1.40  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.86/1.40  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.86/1.40  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k3_subset_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.86/1.40  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.86/1.40  tff(c_26, plain, (~r2_hidden('#skF_4', '#skF_3') | ~r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.86/1.40  tff(c_33, plain, (~r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_26])).
% 2.86/1.40  tff(c_32, plain, (r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3')) | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.86/1.40  tff(c_41, plain, (r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_33, c_32])).
% 2.86/1.40  tff(c_20, plain, (![A_16, B_17]: (m1_subset_1(k7_setfam_1(A_16, B_17), k1_zfmisc_1(k1_zfmisc_1(A_16))) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.86/1.40  tff(c_34, plain, (![A_19, B_20]: (k3_subset_1(A_19, k3_subset_1(A_19, B_20))=B_20 | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.86/1.40  tff(c_40, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_22, c_34])).
% 2.86/1.40  tff(c_138, plain, (![A_32, D_33, B_34]: (r2_hidden(k3_subset_1(A_32, D_33), B_34) | ~r2_hidden(D_33, k7_setfam_1(A_32, B_34)) | ~m1_subset_1(D_33, k1_zfmisc_1(A_32)) | ~m1_subset_1(k7_setfam_1(A_32, B_34), k1_zfmisc_1(k1_zfmisc_1(A_32))) | ~m1_subset_1(B_34, k1_zfmisc_1(k1_zfmisc_1(A_32))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.86/1.40  tff(c_142, plain, (![A_35, D_36, B_37]: (r2_hidden(k3_subset_1(A_35, D_36), B_37) | ~r2_hidden(D_36, k7_setfam_1(A_35, B_37)) | ~m1_subset_1(D_36, k1_zfmisc_1(A_35)) | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(A_35))))), inference(resolution, [status(thm)], [c_20, c_138])).
% 2.86/1.40  tff(c_180, plain, (![A_42, D_43, B_44]: (r2_hidden(k3_subset_1(A_42, D_43), k7_setfam_1(A_42, B_44)) | ~r2_hidden(D_43, k7_setfam_1(A_42, k7_setfam_1(A_42, B_44))) | ~m1_subset_1(D_43, k1_zfmisc_1(A_42)) | ~m1_subset_1(B_44, k1_zfmisc_1(k1_zfmisc_1(A_42))))), inference(resolution, [status(thm)], [c_20, c_142])).
% 2.86/1.40  tff(c_197, plain, (![B_44]: (r2_hidden('#skF_4', k7_setfam_1('#skF_2', B_44)) | ~r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', B_44))) | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(B_44, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_40, c_180])).
% 2.86/1.40  tff(c_202, plain, (~m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_197])).
% 2.86/1.40  tff(c_205, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_2, c_202])).
% 2.86/1.40  tff(c_209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_205])).
% 2.86/1.40  tff(c_211, plain, (m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_197])).
% 2.86/1.40  tff(c_157, plain, (![D_38, A_39, B_40]: (r2_hidden(D_38, k7_setfam_1(A_39, B_40)) | ~r2_hidden(k3_subset_1(A_39, D_38), B_40) | ~m1_subset_1(D_38, k1_zfmisc_1(A_39)) | ~m1_subset_1(k7_setfam_1(A_39, B_40), k1_zfmisc_1(k1_zfmisc_1(A_39))) | ~m1_subset_1(B_40, k1_zfmisc_1(k1_zfmisc_1(A_39))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.86/1.40  tff(c_165, plain, (![B_40]: (r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', B_40)) | ~r2_hidden('#skF_4', B_40) | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k7_setfam_1('#skF_2', B_40), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(B_40, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_40, c_157])).
% 2.86/1.40  tff(c_476, plain, (![B_66]: (r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', B_66)) | ~r2_hidden('#skF_4', B_66) | ~m1_subset_1(k7_setfam_1('#skF_2', B_66), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(B_66, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_165])).
% 2.86/1.40  tff(c_482, plain, (![B_67]: (r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', B_67)) | ~r2_hidden('#skF_4', B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_20, c_476])).
% 2.86/1.40  tff(c_493, plain, (~r2_hidden('#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_482, c_33])).
% 2.86/1.40  tff(c_502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_41, c_493])).
% 2.86/1.40  tff(c_503, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 2.86/1.40  tff(c_504, plain, (r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_26])).
% 2.86/1.40  tff(c_505, plain, (![A_68, B_69]: (k3_subset_1(A_68, k3_subset_1(A_68, B_69))=B_69 | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.86/1.40  tff(c_511, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_22, c_505])).
% 2.86/1.40  tff(c_610, plain, (![A_81, D_82, B_83]: (r2_hidden(k3_subset_1(A_81, D_82), B_83) | ~r2_hidden(D_82, k7_setfam_1(A_81, B_83)) | ~m1_subset_1(D_82, k1_zfmisc_1(A_81)) | ~m1_subset_1(k7_setfam_1(A_81, B_83), k1_zfmisc_1(k1_zfmisc_1(A_81))) | ~m1_subset_1(B_83, k1_zfmisc_1(k1_zfmisc_1(A_81))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.86/1.40  tff(c_614, plain, (![A_84, D_85, B_86]: (r2_hidden(k3_subset_1(A_84, D_85), B_86) | ~r2_hidden(D_85, k7_setfam_1(A_84, B_86)) | ~m1_subset_1(D_85, k1_zfmisc_1(A_84)) | ~m1_subset_1(B_86, k1_zfmisc_1(k1_zfmisc_1(A_84))))), inference(resolution, [status(thm)], [c_20, c_610])).
% 2.86/1.40  tff(c_643, plain, (![D_90]: (r2_hidden(k3_subset_1('#skF_2', D_90), '#skF_3') | ~r2_hidden(D_90, k7_setfam_1('#skF_2', '#skF_3')) | ~m1_subset_1(D_90, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_24, c_614])).
% 2.86/1.40  tff(c_652, plain, (r2_hidden('#skF_4', '#skF_3') | ~r2_hidden(k3_subset_1('#skF_2', '#skF_4'), k7_setfam_1('#skF_2', '#skF_3')) | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_511, c_643])).
% 2.86/1.40  tff(c_657, plain, (r2_hidden('#skF_4', '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_504, c_652])).
% 2.86/1.40  tff(c_658, plain, (~m1_subset_1(k3_subset_1('#skF_2', '#skF_4'), k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_503, c_657])).
% 2.86/1.40  tff(c_661, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_2, c_658])).
% 2.86/1.40  tff(c_665, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_661])).
% 2.86/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.40  
% 2.86/1.40  Inference rules
% 2.86/1.40  ----------------------
% 2.86/1.40  #Ref     : 0
% 2.86/1.40  #Sup     : 152
% 2.86/1.40  #Fact    : 0
% 2.86/1.40  #Define  : 0
% 2.86/1.40  #Split   : 7
% 2.86/1.40  #Chain   : 0
% 2.86/1.40  #Close   : 0
% 2.86/1.40  
% 2.86/1.40  Ordering : KBO
% 2.86/1.40  
% 2.86/1.40  Simplification rules
% 2.86/1.40  ----------------------
% 2.86/1.40  #Subsume      : 16
% 2.86/1.40  #Demod        : 67
% 2.86/1.40  #Tautology    : 63
% 2.86/1.40  #SimpNegUnit  : 4
% 2.86/1.40  #BackRed      : 3
% 2.86/1.40  
% 2.86/1.40  #Partial instantiations: 0
% 2.86/1.40  #Strategies tried      : 1
% 2.86/1.40  
% 2.86/1.40  Timing (in seconds)
% 2.86/1.40  ----------------------
% 2.86/1.41  Preprocessing        : 0.28
% 2.86/1.41  Parsing              : 0.15
% 2.86/1.41  CNF conversion       : 0.02
% 2.86/1.41  Main loop            : 0.36
% 2.86/1.41  Inferencing          : 0.14
% 2.86/1.41  Reduction            : 0.10
% 2.86/1.41  Demodulation         : 0.07
% 2.86/1.41  BG Simplification    : 0.02
% 2.86/1.41  Subsumption          : 0.08
% 2.86/1.41  Abstraction          : 0.02
% 2.86/1.41  MUC search           : 0.00
% 2.86/1.41  Cooper               : 0.00
% 2.86/1.41  Total                : 0.67
% 2.86/1.41  Index Insertion      : 0.00
% 2.86/1.41  Index Deletion       : 0.00
% 2.86/1.41  Index Matching       : 0.00
% 2.86/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
