%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:11 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 113 expanded)
%              Number of leaves         :   20 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   96 ( 232 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v3_setfam_1,type,(
    v3_setfam_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ( v3_setfam_1(B,A)
                & r1_tarski(C,B) )
             => v3_setfam_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_setfam_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v3_setfam_1(B,A)
      <=> ~ r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_68,plain,(
    ! [A_29,C_30,B_31] :
      ( m1_subset_1(A_29,C_30)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(C_30))
      | ~ r2_hidden(A_29,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_78,plain,(
    ! [A_32] :
      ( m1_subset_1(A_32,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_32,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_68])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_90,plain,(
    ! [A_33] :
      ( r1_tarski(A_33,'#skF_2')
      | ~ r2_hidden(A_33,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_78,c_14])).

tff(c_100,plain,
    ( r1_tarski('#skF_1'('#skF_4'),'#skF_2')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_90])).

tff(c_124,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_20,plain,(
    ~ v3_setfam_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_175,plain,(
    ! [B_43,A_44] :
      ( v3_setfam_1(B_43,A_44)
      | r2_hidden(A_44,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(A_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_185,plain,
    ( v3_setfam_1('#skF_4','#skF_2')
    | r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_175])).

tff(c_192,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_185])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_200,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_192,c_2])).

tff(c_206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_200])).

tff(c_208,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_101,plain,(
    ! [A_34] :
      ( m1_subset_1(A_34,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_34,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_68])).

tff(c_113,plain,(
    ! [A_35] :
      ( r1_tarski(A_35,'#skF_2')
      | ~ r2_hidden(A_35,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_101,c_14])).

tff(c_123,plain,
    ( r1_tarski('#skF_1'('#skF_3'),'#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_113])).

tff(c_210,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_22,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_54,plain,(
    ! [B_27,A_28] :
      ( v1_xboole_0(B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_28))
      | ~ v1_xboole_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_211,plain,(
    ! [A_45,B_46] :
      ( v1_xboole_0(A_45)
      | ~ v1_xboole_0(B_46)
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(resolution,[status(thm)],[c_16,c_54])).

tff(c_223,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_211])).

tff(c_231,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_223])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_231])).

tff(c_235,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24,plain,(
    v3_setfam_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_331,plain,(
    ! [A_57,B_58] :
      ( ~ r2_hidden(A_57,B_58)
      | ~ v3_setfam_1(B_58,A_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k1_zfmisc_1(A_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_338,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | ~ v3_setfam_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_331])).

tff(c_345,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_338])).

tff(c_351,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_345])).

tff(c_354,plain,(
    ~ m1_subset_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_235,c_351])).

tff(c_236,plain,(
    ! [B_47,A_48] :
      ( v3_setfam_1(B_47,A_48)
      | r2_hidden(A_48,B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_246,plain,
    ( v3_setfam_1('#skF_4','#skF_2')
    | r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_236])).

tff(c_252,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_246])).

tff(c_302,plain,(
    ! [A_53,B_54,A_55] :
      ( m1_subset_1(A_53,B_54)
      | ~ r2_hidden(A_53,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(resolution,[status(thm)],[c_16,c_68])).

tff(c_312,plain,(
    ! [B_56] :
      ( m1_subset_1('#skF_2',B_56)
      | ~ r1_tarski('#skF_4',B_56) ) ),
    inference(resolution,[status(thm)],[c_252,c_302])).

tff(c_330,plain,(
    m1_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_312])).

tff(c_355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_354,c_330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.66  
% 2.56/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.67  %$ v3_setfam_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.56/1.67  
% 2.56/1.67  %Foreground sorts:
% 2.56/1.67  
% 2.56/1.67  
% 2.56/1.67  %Background operators:
% 2.56/1.67  
% 2.56/1.67  
% 2.56/1.67  %Foreground operators:
% 2.56/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.67  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.56/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.67  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.67  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.67  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.67  tff(v3_setfam_1, type, v3_setfam_1: ($i * $i) > $o).
% 2.56/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.56/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.67  
% 2.81/1.69  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.81/1.69  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((v3_setfam_1(B, A) & r1_tarski(C, B)) => v3_setfam_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_setfam_1)).
% 2.81/1.69  tff(f_61, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.81/1.69  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.81/1.69  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v3_setfam_1(B, A) <=> ~r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_setfam_1)).
% 2.81/1.69  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.81/1.69  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.81/1.69  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.69  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.81/1.69  tff(c_68, plain, (![A_29, C_30, B_31]: (m1_subset_1(A_29, C_30) | ~m1_subset_1(B_31, k1_zfmisc_1(C_30)) | ~r2_hidden(A_29, B_31))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.81/1.69  tff(c_78, plain, (![A_32]: (m1_subset_1(A_32, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_32, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_68])).
% 2.81/1.69  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.81/1.69  tff(c_90, plain, (![A_33]: (r1_tarski(A_33, '#skF_2') | ~r2_hidden(A_33, '#skF_4'))), inference(resolution, [status(thm)], [c_78, c_14])).
% 2.81/1.69  tff(c_100, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_2') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_90])).
% 2.81/1.69  tff(c_124, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_100])).
% 2.81/1.69  tff(c_20, plain, (~v3_setfam_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.81/1.69  tff(c_175, plain, (![B_43, A_44]: (v3_setfam_1(B_43, A_44) | r2_hidden(A_44, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(A_44))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.81/1.69  tff(c_185, plain, (v3_setfam_1('#skF_4', '#skF_2') | r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_175])).
% 2.81/1.69  tff(c_192, plain, (r2_hidden('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_20, c_185])).
% 2.81/1.69  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.69  tff(c_200, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_192, c_2])).
% 2.81/1.69  tff(c_206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_124, c_200])).
% 2.81/1.69  tff(c_208, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_100])).
% 2.81/1.69  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.81/1.69  tff(c_101, plain, (![A_34]: (m1_subset_1(A_34, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_34, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_68])).
% 2.81/1.69  tff(c_113, plain, (![A_35]: (r1_tarski(A_35, '#skF_2') | ~r2_hidden(A_35, '#skF_3'))), inference(resolution, [status(thm)], [c_101, c_14])).
% 2.81/1.69  tff(c_123, plain, (r1_tarski('#skF_1'('#skF_3'), '#skF_2') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_113])).
% 2.81/1.69  tff(c_210, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_123])).
% 2.81/1.69  tff(c_22, plain, (r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.81/1.69  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.81/1.69  tff(c_54, plain, (![B_27, A_28]: (v1_xboole_0(B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(A_28)) | ~v1_xboole_0(A_28))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.81/1.69  tff(c_211, plain, (![A_45, B_46]: (v1_xboole_0(A_45) | ~v1_xboole_0(B_46) | ~r1_tarski(A_45, B_46))), inference(resolution, [status(thm)], [c_16, c_54])).
% 2.81/1.69  tff(c_223, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_22, c_211])).
% 2.81/1.69  tff(c_231, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_223])).
% 2.81/1.69  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_208, c_231])).
% 2.81/1.69  tff(c_235, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_123])).
% 2.81/1.69  tff(c_12, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.81/1.69  tff(c_24, plain, (v3_setfam_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.81/1.69  tff(c_331, plain, (![A_57, B_58]: (~r2_hidden(A_57, B_58) | ~v3_setfam_1(B_58, A_57) | ~m1_subset_1(B_58, k1_zfmisc_1(k1_zfmisc_1(A_57))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.81/1.69  tff(c_338, plain, (~r2_hidden('#skF_2', '#skF_3') | ~v3_setfam_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_331])).
% 2.81/1.69  tff(c_345, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_338])).
% 2.81/1.69  tff(c_351, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_345])).
% 2.81/1.69  tff(c_354, plain, (~m1_subset_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_235, c_351])).
% 2.81/1.69  tff(c_236, plain, (![B_47, A_48]: (v3_setfam_1(B_47, A_48) | r2_hidden(A_48, B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(k1_zfmisc_1(A_48))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.81/1.69  tff(c_246, plain, (v3_setfam_1('#skF_4', '#skF_2') | r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_236])).
% 2.81/1.69  tff(c_252, plain, (r2_hidden('#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_20, c_246])).
% 2.81/1.69  tff(c_302, plain, (![A_53, B_54, A_55]: (m1_subset_1(A_53, B_54) | ~r2_hidden(A_53, A_55) | ~r1_tarski(A_55, B_54))), inference(resolution, [status(thm)], [c_16, c_68])).
% 2.81/1.69  tff(c_312, plain, (![B_56]: (m1_subset_1('#skF_2', B_56) | ~r1_tarski('#skF_4', B_56))), inference(resolution, [status(thm)], [c_252, c_302])).
% 2.81/1.69  tff(c_330, plain, (m1_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_312])).
% 2.81/1.69  tff(c_355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_354, c_330])).
% 2.81/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.69  
% 2.81/1.69  Inference rules
% 2.81/1.69  ----------------------
% 2.81/1.69  #Ref     : 0
% 2.81/1.69  #Sup     : 64
% 2.81/1.69  #Fact    : 0
% 2.81/1.69  #Define  : 0
% 2.81/1.69  #Split   : 7
% 2.81/1.69  #Chain   : 0
% 2.81/1.69  #Close   : 0
% 2.81/1.69  
% 2.81/1.69  Ordering : KBO
% 2.81/1.69  
% 2.81/1.69  Simplification rules
% 2.81/1.69  ----------------------
% 2.81/1.69  #Subsume      : 19
% 2.81/1.69  #Demod        : 15
% 2.81/1.69  #Tautology    : 9
% 2.81/1.69  #SimpNegUnit  : 13
% 2.81/1.69  #BackRed      : 0
% 2.81/1.69  
% 2.81/1.69  #Partial instantiations: 0
% 2.81/1.69  #Strategies tried      : 1
% 2.81/1.69  
% 2.81/1.69  Timing (in seconds)
% 2.81/1.69  ----------------------
% 2.81/1.70  Preprocessing        : 0.44
% 2.81/1.70  Parsing              : 0.24
% 2.81/1.70  CNF conversion       : 0.03
% 2.81/1.70  Main loop            : 0.37
% 2.81/1.70  Inferencing          : 0.16
% 2.81/1.70  Reduction            : 0.10
% 2.81/1.70  Demodulation         : 0.07
% 2.81/1.70  BG Simplification    : 0.02
% 2.81/1.70  Subsumption          : 0.05
% 2.81/1.70  Abstraction          : 0.01
% 2.81/1.70  MUC search           : 0.00
% 2.81/1.70  Cooper               : 0.00
% 2.81/1.70  Total                : 0.86
% 2.81/1.70  Index Insertion      : 0.00
% 2.81/1.70  Index Deletion       : 0.00
% 2.81/1.70  Index Matching       : 0.00
% 2.81/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
