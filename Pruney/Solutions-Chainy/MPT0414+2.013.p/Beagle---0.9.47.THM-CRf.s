%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:44 EST 2020

% Result     : Theorem 8.98s
% Output     : CNFRefutation 8.98s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 104 expanded)
%              Number of leaves         :   22 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 243 expanded)
%              Number of equality atoms :   11 (  25 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(A))
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( ! [C] :
            ( m1_subset_1(C,A)
           => r2_hidden(C,B) )
       => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_26,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_141,plain,(
    ! [A_55,C_56,B_57] :
      ( m1_subset_1(A_55,C_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(C_56))
      | ~ r2_hidden(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_151,plain,(
    ! [A_58] :
      ( m1_subset_1(A_58,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(A_58,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_28,c_141])).

tff(c_32,plain,(
    ! [D_26] :
      ( r2_hidden(D_26,'#skF_5')
      | ~ r2_hidden(D_26,'#skF_6')
      | ~ m1_subset_1(D_26,k1_zfmisc_1('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_167,plain,(
    ! [A_59] :
      ( r2_hidden(A_59,'#skF_5')
      | ~ r2_hidden(A_59,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_151,c_32])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_387,plain,(
    ! [A_72] :
      ( r1_tarski(A_72,'#skF_5')
      | ~ r2_hidden('#skF_2'(A_72,'#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_167,c_8])).

tff(c_399,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_387])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1('#skF_3'(A_12,B_13),A_12)
      | B_13 = A_12
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56,plain,(
    ! [D_36] :
      ( r2_hidden(D_36,'#skF_5')
      | ~ r2_hidden(D_36,'#skF_6')
      | ~ m1_subset_1(D_36,k1_zfmisc_1('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_127,plain,(
    ! [A_54] :
      ( r2_hidden(A_54,'#skF_5')
      | ~ r2_hidden(A_54,'#skF_6')
      | ~ r1_tarski(A_54,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_56])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,(
    ! [A_54] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(A_54,'#skF_6')
      | ~ r1_tarski(A_54,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_127,c_2])).

tff(c_140,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_180,plain,(
    ! [A_60] :
      ( m1_subset_1(A_60,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(A_60,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_141])).

tff(c_34,plain,(
    ! [D_26] :
      ( r2_hidden(D_26,'#skF_6')
      | ~ r2_hidden(D_26,'#skF_5')
      | ~ m1_subset_1(D_26,k1_zfmisc_1('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_213,plain,(
    ! [A_62] :
      ( r2_hidden(A_62,'#skF_6')
      | ~ r2_hidden(A_62,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_180,c_34])).

tff(c_228,plain,(
    ! [A_15] :
      ( r2_hidden(A_15,'#skF_6')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(A_15,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_18,c_213])).

tff(c_238,plain,(
    ! [A_15] :
      ( r2_hidden(A_15,'#skF_6')
      | ~ m1_subset_1(A_15,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_228])).

tff(c_371,plain,(
    ! [A_70,B_71] :
      ( ~ r2_hidden('#skF_3'(A_70,B_71),B_71)
      | B_71 = A_70
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_13384,plain,(
    ! [A_485] :
      ( A_485 = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_485))
      | ~ m1_subset_1('#skF_3'(A_485,'#skF_6'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_238,c_371])).

tff(c_13391,plain,
    ( '#skF_5' = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_16,c_13384])).

tff(c_13395,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_13391])).

tff(c_13398,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_13395])).

tff(c_13402,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_399,c_13398])).

tff(c_13404,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_13435,plain,(
    ! [A_488,C_489,B_490] :
      ( m1_subset_1(A_488,C_489)
      | ~ m1_subset_1(B_490,k1_zfmisc_1(C_489))
      | ~ r2_hidden(A_488,B_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_13512,plain,(
    ! [A_494] :
      ( m1_subset_1(A_494,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(A_494,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_28,c_13435])).

tff(c_13524,plain,(
    ! [A_495] :
      ( r2_hidden(A_495,'#skF_5')
      | ~ r2_hidden(A_495,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_13512,c_32])).

tff(c_13539,plain,(
    ! [A_495] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(A_495,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_13524,c_2])).

tff(c_13548,plain,(
    ! [A_496] : ~ r2_hidden(A_496,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13404,c_13539])).

tff(c_13568,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_13548])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( ~ v1_xboole_0(B_11)
      | B_11 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_13407,plain,(
    ! [A_10] :
      ( A_10 = '#skF_5'
      | ~ v1_xboole_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_13404,c_12])).

tff(c_13581,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_13568,c_13407])).

tff(c_13587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_13581])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:02:30 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.98/3.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.98/3.14  
% 8.98/3.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.98/3.15  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 8.98/3.15  
% 8.98/3.15  %Foreground sorts:
% 8.98/3.15  
% 8.98/3.15  
% 8.98/3.15  %Background operators:
% 8.98/3.15  
% 8.98/3.15  
% 8.98/3.15  %Foreground operators:
% 8.98/3.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.98/3.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.98/3.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.98/3.15  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.98/3.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.98/3.15  tff('#skF_5', type, '#skF_5': $i).
% 8.98/3.15  tff('#skF_6', type, '#skF_6': $i).
% 8.98/3.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.98/3.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.98/3.15  tff('#skF_4', type, '#skF_4': $i).
% 8.98/3.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.98/3.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.98/3.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.98/3.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.98/3.15  
% 8.98/3.16  tff(f_86, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_setfam_1)).
% 8.98/3.16  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.98/3.16  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.98/3.16  tff(f_71, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 8.98/3.16  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.98/3.16  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 8.98/3.16  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 8.98/3.16  tff(f_46, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 8.98/3.16  tff(c_26, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.98/3.16  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.98/3.16  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.98/3.16  tff(c_28, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.98/3.16  tff(c_141, plain, (![A_55, C_56, B_57]: (m1_subset_1(A_55, C_56) | ~m1_subset_1(B_57, k1_zfmisc_1(C_56)) | ~r2_hidden(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.98/3.16  tff(c_151, plain, (![A_58]: (m1_subset_1(A_58, k1_zfmisc_1('#skF_4')) | ~r2_hidden(A_58, '#skF_6'))), inference(resolution, [status(thm)], [c_28, c_141])).
% 8.98/3.16  tff(c_32, plain, (![D_26]: (r2_hidden(D_26, '#skF_5') | ~r2_hidden(D_26, '#skF_6') | ~m1_subset_1(D_26, k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.98/3.16  tff(c_167, plain, (![A_59]: (r2_hidden(A_59, '#skF_5') | ~r2_hidden(A_59, '#skF_6'))), inference(resolution, [status(thm)], [c_151, c_32])).
% 8.98/3.16  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.98/3.16  tff(c_387, plain, (![A_72]: (r1_tarski(A_72, '#skF_5') | ~r2_hidden('#skF_2'(A_72, '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_167, c_8])).
% 8.98/3.16  tff(c_399, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_10, c_387])).
% 8.98/3.16  tff(c_22, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.98/3.16  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1('#skF_3'(A_12, B_13), A_12) | B_13=A_12 | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.98/3.16  tff(c_56, plain, (![D_36]: (r2_hidden(D_36, '#skF_5') | ~r2_hidden(D_36, '#skF_6') | ~m1_subset_1(D_36, k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.98/3.16  tff(c_127, plain, (![A_54]: (r2_hidden(A_54, '#skF_5') | ~r2_hidden(A_54, '#skF_6') | ~r1_tarski(A_54, '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_56])).
% 8.98/3.16  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.98/3.16  tff(c_139, plain, (![A_54]: (~v1_xboole_0('#skF_5') | ~r2_hidden(A_54, '#skF_6') | ~r1_tarski(A_54, '#skF_4'))), inference(resolution, [status(thm)], [c_127, c_2])).
% 8.98/3.16  tff(c_140, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_139])).
% 8.98/3.16  tff(c_18, plain, (![A_15, B_16]: (r2_hidden(A_15, B_16) | v1_xboole_0(B_16) | ~m1_subset_1(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.98/3.16  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.98/3.16  tff(c_180, plain, (![A_60]: (m1_subset_1(A_60, k1_zfmisc_1('#skF_4')) | ~r2_hidden(A_60, '#skF_5'))), inference(resolution, [status(thm)], [c_30, c_141])).
% 8.98/3.16  tff(c_34, plain, (![D_26]: (r2_hidden(D_26, '#skF_6') | ~r2_hidden(D_26, '#skF_5') | ~m1_subset_1(D_26, k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.98/3.16  tff(c_213, plain, (![A_62]: (r2_hidden(A_62, '#skF_6') | ~r2_hidden(A_62, '#skF_5'))), inference(resolution, [status(thm)], [c_180, c_34])).
% 8.98/3.16  tff(c_228, plain, (![A_15]: (r2_hidden(A_15, '#skF_6') | v1_xboole_0('#skF_5') | ~m1_subset_1(A_15, '#skF_5'))), inference(resolution, [status(thm)], [c_18, c_213])).
% 8.98/3.16  tff(c_238, plain, (![A_15]: (r2_hidden(A_15, '#skF_6') | ~m1_subset_1(A_15, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_140, c_228])).
% 8.98/3.16  tff(c_371, plain, (![A_70, B_71]: (~r2_hidden('#skF_3'(A_70, B_71), B_71) | B_71=A_70 | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.98/3.16  tff(c_13384, plain, (![A_485]: (A_485='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_485)) | ~m1_subset_1('#skF_3'(A_485, '#skF_6'), '#skF_5'))), inference(resolution, [status(thm)], [c_238, c_371])).
% 8.98/3.16  tff(c_13391, plain, ('#skF_5'='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_13384])).
% 8.98/3.16  tff(c_13395, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_13391])).
% 8.98/3.16  tff(c_13398, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_22, c_13395])).
% 8.98/3.16  tff(c_13402, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_399, c_13398])).
% 8.98/3.16  tff(c_13404, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_139])).
% 8.98/3.16  tff(c_13435, plain, (![A_488, C_489, B_490]: (m1_subset_1(A_488, C_489) | ~m1_subset_1(B_490, k1_zfmisc_1(C_489)) | ~r2_hidden(A_488, B_490))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.98/3.16  tff(c_13512, plain, (![A_494]: (m1_subset_1(A_494, k1_zfmisc_1('#skF_4')) | ~r2_hidden(A_494, '#skF_6'))), inference(resolution, [status(thm)], [c_28, c_13435])).
% 8.98/3.16  tff(c_13524, plain, (![A_495]: (r2_hidden(A_495, '#skF_5') | ~r2_hidden(A_495, '#skF_6'))), inference(resolution, [status(thm)], [c_13512, c_32])).
% 8.98/3.16  tff(c_13539, plain, (![A_495]: (~v1_xboole_0('#skF_5') | ~r2_hidden(A_495, '#skF_6'))), inference(resolution, [status(thm)], [c_13524, c_2])).
% 8.98/3.16  tff(c_13548, plain, (![A_496]: (~r2_hidden(A_496, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_13404, c_13539])).
% 8.98/3.16  tff(c_13568, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_13548])).
% 8.98/3.16  tff(c_12, plain, (![B_11, A_10]: (~v1_xboole_0(B_11) | B_11=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.98/3.16  tff(c_13407, plain, (![A_10]: (A_10='#skF_5' | ~v1_xboole_0(A_10))), inference(resolution, [status(thm)], [c_13404, c_12])).
% 8.98/3.16  tff(c_13581, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_13568, c_13407])).
% 8.98/3.16  tff(c_13587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_13581])).
% 8.98/3.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.98/3.16  
% 8.98/3.16  Inference rules
% 8.98/3.16  ----------------------
% 8.98/3.16  #Ref     : 0
% 8.98/3.16  #Sup     : 2906
% 8.98/3.16  #Fact    : 0
% 8.98/3.16  #Define  : 0
% 8.98/3.16  #Split   : 28
% 8.98/3.16  #Chain   : 0
% 8.98/3.16  #Close   : 0
% 8.98/3.16  
% 8.98/3.16  Ordering : KBO
% 8.98/3.16  
% 8.98/3.16  Simplification rules
% 8.98/3.16  ----------------------
% 8.98/3.16  #Subsume      : 1396
% 8.98/3.16  #Demod        : 1444
% 8.98/3.16  #Tautology    : 495
% 8.98/3.16  #SimpNegUnit  : 348
% 8.98/3.16  #BackRed      : 179
% 8.98/3.16  
% 8.98/3.16  #Partial instantiations: 0
% 8.98/3.16  #Strategies tried      : 1
% 8.98/3.16  
% 8.98/3.16  Timing (in seconds)
% 8.98/3.16  ----------------------
% 8.98/3.16  Preprocessing        : 0.30
% 8.98/3.16  Parsing              : 0.17
% 8.98/3.16  CNF conversion       : 0.02
% 8.98/3.16  Main loop            : 2.08
% 8.98/3.16  Inferencing          : 0.60
% 8.98/3.16  Reduction            : 0.60
% 8.98/3.16  Demodulation         : 0.35
% 8.98/3.16  BG Simplification    : 0.06
% 8.98/3.16  Subsumption          : 0.63
% 8.98/3.16  Abstraction          : 0.07
% 8.98/3.16  MUC search           : 0.00
% 8.98/3.16  Cooper               : 0.00
% 8.98/3.16  Total                : 2.41
% 8.98/3.16  Index Insertion      : 0.00
% 8.98/3.16  Index Deletion       : 0.00
% 8.98/3.17  Index Matching       : 0.00
% 8.98/3.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
