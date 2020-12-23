%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:38 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 103 expanded)
%              Number of leaves         :   19 (  42 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 211 expanded)
%              Number of equality atoms :   30 ( 128 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_setfam_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( ~ ( B != k1_xboole_0
              & k7_setfam_1(A,B) = k1_xboole_0 )
          & ~ ( k7_setfam_1(A,B) != k1_xboole_0
              & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tops_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(c_36,plain,
    ( k1_xboole_0 != '#skF_3'
    | k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_67,plain,(
    k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_30,plain,
    ( k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_68,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_30])).

tff(c_69,plain,(
    k7_setfam_1('#skF_2','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_67])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_22,B_23] : ~ r2_hidden(A_22,k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_62,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_70,plain,(
    ! [A_1] : ~ r2_hidden(A_1,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_62])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_270,plain,(
    ! [A_59,B_60,C_61] :
      ( r2_hidden('#skF_1'(A_59,B_60,C_61),C_61)
      | r2_hidden(k3_subset_1(A_59,'#skF_1'(A_59,B_60,C_61)),B_60)
      | k7_setfam_1(A_59,B_60) = C_61
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k1_zfmisc_1(A_59)))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(A_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_291,plain,(
    ! [A_62,C_63] :
      ( r2_hidden('#skF_1'(A_62,'#skF_3',C_63),C_63)
      | k7_setfam_1(A_62,'#skF_3') = C_63
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k1_zfmisc_1(A_62)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_62))) ) ),
    inference(resolution,[status(thm)],[c_270,c_70])).

tff(c_298,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3')
    | k7_setfam_1('#skF_2','#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_28,c_291])).

tff(c_303,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3')
    | k7_setfam_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_298])).

tff(c_305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_70,c_303])).

tff(c_306,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_307,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_337,plain,(
    ! [A_68,B_69] :
      ( m1_subset_1(k7_setfam_1(A_68,B_69),k1_zfmisc_1(k1_zfmisc_1(A_68)))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k1_zfmisc_1(A_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_345,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_337])).

tff(c_349,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_345])).

tff(c_328,plain,(
    ! [A_66,B_67] :
      ( k7_setfam_1(A_66,k7_setfam_1(A_66,B_67)) = B_67
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(A_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_330,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_328])).

tff(c_332,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_330])).

tff(c_509,plain,(
    ! [A_97,B_98,C_99] :
      ( r2_hidden('#skF_1'(A_97,B_98,C_99),C_99)
      | r2_hidden(k3_subset_1(A_97,'#skF_1'(A_97,B_98,C_99)),B_98)
      | k7_setfam_1(A_97,B_98) = C_99
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k1_zfmisc_1(A_97)))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k1_zfmisc_1(A_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_524,plain,(
    ! [A_100,C_101] :
      ( r2_hidden('#skF_1'(A_100,k1_xboole_0,C_101),C_101)
      | k7_setfam_1(A_100,k1_xboole_0) = C_101
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k1_zfmisc_1(A_100)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_100))) ) ),
    inference(resolution,[status(thm)],[c_509,c_62])).

tff(c_529,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k7_setfam_1('#skF_2',k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_349,c_524])).

tff(c_537,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_332,c_529])).

tff(c_539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_62,c_537])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.38  
% 2.51/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.39  %$ r2_hidden > m1_subset_1 > k7_setfam_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.51/1.39  
% 2.51/1.39  %Foreground sorts:
% 2.51/1.39  
% 2.51/1.39  
% 2.51/1.39  %Background operators:
% 2.51/1.39  
% 2.51/1.39  
% 2.51/1.39  %Foreground operators:
% 2.51/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.51/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.39  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.51/1.39  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.51/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.51/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.39  
% 2.51/1.40  tff(f_71, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)) & ~(~(k7_setfam_1(A, B) = k1_xboole_0) & (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tops_2)).
% 2.51/1.40  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.51/1.40  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.51/1.40  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.51/1.40  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 2.51/1.40  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.51/1.40  tff(c_36, plain, (k1_xboole_0!='#skF_3' | k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.51/1.40  tff(c_67, plain, (k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 2.51/1.40  tff(c_30, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.51/1.40  tff(c_68, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_67, c_30])).
% 2.51/1.40  tff(c_69, plain, (k7_setfam_1('#skF_2', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_67])).
% 2.51/1.40  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.51/1.40  tff(c_59, plain, (![A_22, B_23]: (~r2_hidden(A_22, k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.51/1.40  tff(c_62, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_59])).
% 2.51/1.40  tff(c_70, plain, (![A_1]: (~r2_hidden(A_1, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_62])).
% 2.51/1.40  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.51/1.40  tff(c_270, plain, (![A_59, B_60, C_61]: (r2_hidden('#skF_1'(A_59, B_60, C_61), C_61) | r2_hidden(k3_subset_1(A_59, '#skF_1'(A_59, B_60, C_61)), B_60) | k7_setfam_1(A_59, B_60)=C_61 | ~m1_subset_1(C_61, k1_zfmisc_1(k1_zfmisc_1(A_59))) | ~m1_subset_1(B_60, k1_zfmisc_1(k1_zfmisc_1(A_59))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.51/1.40  tff(c_291, plain, (![A_62, C_63]: (r2_hidden('#skF_1'(A_62, '#skF_3', C_63), C_63) | k7_setfam_1(A_62, '#skF_3')=C_63 | ~m1_subset_1(C_63, k1_zfmisc_1(k1_zfmisc_1(A_62))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_62))))), inference(resolution, [status(thm)], [c_270, c_70])).
% 2.51/1.40  tff(c_298, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3') | k7_setfam_1('#skF_2', '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_28, c_291])).
% 2.51/1.40  tff(c_303, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3') | k7_setfam_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_298])).
% 2.51/1.40  tff(c_305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_70, c_303])).
% 2.51/1.40  tff(c_306, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_36])).
% 2.51/1.40  tff(c_307, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.51/1.40  tff(c_337, plain, (![A_68, B_69]: (m1_subset_1(k7_setfam_1(A_68, B_69), k1_zfmisc_1(k1_zfmisc_1(A_68))) | ~m1_subset_1(B_69, k1_zfmisc_1(k1_zfmisc_1(A_68))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.51/1.40  tff(c_345, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_307, c_337])).
% 2.51/1.40  tff(c_349, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_345])).
% 2.51/1.40  tff(c_328, plain, (![A_66, B_67]: (k7_setfam_1(A_66, k7_setfam_1(A_66, B_67))=B_67 | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1(A_66))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.51/1.40  tff(c_330, plain, (k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_28, c_328])).
% 2.51/1.40  tff(c_332, plain, (k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_307, c_330])).
% 2.51/1.40  tff(c_509, plain, (![A_97, B_98, C_99]: (r2_hidden('#skF_1'(A_97, B_98, C_99), C_99) | r2_hidden(k3_subset_1(A_97, '#skF_1'(A_97, B_98, C_99)), B_98) | k7_setfam_1(A_97, B_98)=C_99 | ~m1_subset_1(C_99, k1_zfmisc_1(k1_zfmisc_1(A_97))) | ~m1_subset_1(B_98, k1_zfmisc_1(k1_zfmisc_1(A_97))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.51/1.40  tff(c_524, plain, (![A_100, C_101]: (r2_hidden('#skF_1'(A_100, k1_xboole_0, C_101), C_101) | k7_setfam_1(A_100, k1_xboole_0)=C_101 | ~m1_subset_1(C_101, k1_zfmisc_1(k1_zfmisc_1(A_100))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_100))))), inference(resolution, [status(thm)], [c_509, c_62])).
% 2.51/1.40  tff(c_529, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1('#skF_2', k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_349, c_524])).
% 2.51/1.40  tff(c_537, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, k1_xboole_0), k1_xboole_0) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_349, c_332, c_529])).
% 2.51/1.40  tff(c_539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_306, c_62, c_537])).
% 2.51/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.40  
% 2.51/1.40  Inference rules
% 2.51/1.40  ----------------------
% 2.51/1.40  #Ref     : 0
% 2.51/1.40  #Sup     : 118
% 2.51/1.40  #Fact    : 0
% 2.51/1.40  #Define  : 0
% 2.51/1.40  #Split   : 2
% 2.51/1.40  #Chain   : 0
% 2.51/1.40  #Close   : 0
% 2.51/1.40  
% 2.51/1.40  Ordering : KBO
% 2.51/1.40  
% 2.51/1.40  Simplification rules
% 2.51/1.40  ----------------------
% 2.51/1.40  #Subsume      : 20
% 2.51/1.40  #Demod        : 76
% 2.51/1.40  #Tautology    : 65
% 2.51/1.40  #SimpNegUnit  : 9
% 2.51/1.40  #BackRed      : 4
% 2.51/1.40  
% 2.51/1.40  #Partial instantiations: 0
% 2.51/1.40  #Strategies tried      : 1
% 2.51/1.40  
% 2.51/1.40  Timing (in seconds)
% 2.51/1.40  ----------------------
% 2.51/1.40  Preprocessing        : 0.31
% 2.51/1.40  Parsing              : 0.17
% 2.51/1.40  CNF conversion       : 0.02
% 2.51/1.40  Main loop            : 0.28
% 2.51/1.40  Inferencing          : 0.11
% 2.51/1.40  Reduction            : 0.08
% 2.51/1.40  Demodulation         : 0.05
% 2.51/1.40  BG Simplification    : 0.02
% 2.51/1.40  Subsumption          : 0.06
% 2.51/1.40  Abstraction          : 0.02
% 2.51/1.40  MUC search           : 0.00
% 2.51/1.40  Cooper               : 0.00
% 2.51/1.40  Total                : 0.61
% 2.51/1.40  Index Insertion      : 0.00
% 2.51/1.40  Index Deletion       : 0.00
% 2.51/1.40  Index Matching       : 0.00
% 2.51/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
