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
% DateTime   : Thu Dec  3 10:28:25 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   56 (  61 expanded)
%              Number of leaves         :   29 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 (  93 expanded)
%              Number of equality atoms :   26 (  28 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_70,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(A_19,B_20)
      | k4_xboole_0(A_19,B_20) != A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_174,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ r1_xboole_0(A_60,B_61)
      | ~ r2_hidden(C_62,k3_xboole_0(A_60,B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_341,plain,(
    ! [A_86,B_87] :
      ( ~ r1_xboole_0(A_86,B_87)
      | v1_xboole_0(k3_xboole_0(A_86,B_87)) ) ),
    inference(resolution,[status(thm)],[c_4,c_174])).

tff(c_40,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_358,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_341,c_40])).

tff(c_370,plain,(
    k4_xboole_0('#skF_4','#skF_5') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_358])).

tff(c_22,plain,(
    ! [A_17,B_18] : r1_tarski(k4_xboole_0(A_17,B_18),A_17) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_76,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(A_46,B_47) = k1_xboole_0
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_84,plain,(
    ! [A_17,B_18] : k4_xboole_0(k4_xboole_0(A_17,B_18),A_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_76])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_42,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | k4_xboole_0(A_15,B_16) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_398,plain,(
    ! [B_94,A_95] :
      ( B_94 = A_95
      | ~ r1_tarski(A_95,B_94)
      | ~ v1_zfmisc_1(B_94)
      | v1_xboole_0(B_94)
      | v1_xboole_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_755,plain,(
    ! [B_123,A_124] :
      ( B_123 = A_124
      | ~ v1_zfmisc_1(B_123)
      | v1_xboole_0(B_123)
      | v1_xboole_0(A_124)
      | k4_xboole_0(A_124,B_123) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_398])).

tff(c_757,plain,(
    ! [A_124] :
      ( A_124 = '#skF_4'
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(A_124)
      | k4_xboole_0(A_124,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_755])).

tff(c_840,plain,(
    ! [A_131] :
      ( A_131 = '#skF_4'
      | v1_xboole_0(A_131)
      | k4_xboole_0(A_131,'#skF_4') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_757])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [B_39,A_40] :
      ( ~ v1_xboole_0(B_39)
      | B_39 = A_40
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_55,plain,(
    ! [A_40] :
      ( k1_xboole_0 = A_40
      | ~ v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_6,c_52])).

tff(c_1263,plain,(
    ! [A_149] :
      ( k1_xboole_0 = A_149
      | A_149 = '#skF_4'
      | k4_xboole_0(A_149,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_840,c_55])).

tff(c_1294,plain,(
    ! [B_150] :
      ( k4_xboole_0('#skF_4',B_150) = k1_xboole_0
      | k4_xboole_0('#skF_4',B_150) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_1263])).

tff(c_56,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | k4_xboole_0(A_41,B_42) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_60,plain,(
    k4_xboole_0('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_38])).

tff(c_1333,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1294,c_60])).

tff(c_1379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_1333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:52:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.42  
% 2.80/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.42  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.80/1.42  
% 2.80/1.42  %Foreground sorts:
% 2.80/1.42  
% 2.80/1.42  
% 2.80/1.42  %Background operators:
% 2.80/1.42  
% 2.80/1.42  
% 2.80/1.42  %Foreground operators:
% 2.80/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.80/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.80/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.80/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.80/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.80/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.80/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.80/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.80/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.80/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.80/1.42  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.80/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.80/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.80/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.80/1.42  
% 2.80/1.43  tff(f_74, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.80/1.43  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.80/1.43  tff(f_64, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.80/1.43  tff(f_113, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 2.80/1.43  tff(f_70, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.80/1.43  tff(f_68, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.80/1.43  tff(f_101, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.80/1.43  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.80/1.43  tff(f_82, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.80/1.43  tff(c_26, plain, (![A_19, B_20]: (r1_xboole_0(A_19, B_20) | k4_xboole_0(A_19, B_20)!=A_19)), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.80/1.43  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.43  tff(c_174, plain, (![A_60, B_61, C_62]: (~r1_xboole_0(A_60, B_61) | ~r2_hidden(C_62, k3_xboole_0(A_60, B_61)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.80/1.43  tff(c_341, plain, (![A_86, B_87]: (~r1_xboole_0(A_86, B_87) | v1_xboole_0(k3_xboole_0(A_86, B_87)))), inference(resolution, [status(thm)], [c_4, c_174])).
% 2.80/1.43  tff(c_40, plain, (~v1_xboole_0(k3_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.80/1.43  tff(c_358, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_341, c_40])).
% 2.80/1.43  tff(c_370, plain, (k4_xboole_0('#skF_4', '#skF_5')!='#skF_4'), inference(resolution, [status(thm)], [c_26, c_358])).
% 2.80/1.43  tff(c_22, plain, (![A_17, B_18]: (r1_tarski(k4_xboole_0(A_17, B_18), A_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.80/1.43  tff(c_76, plain, (![A_46, B_47]: (k4_xboole_0(A_46, B_47)=k1_xboole_0 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.80/1.43  tff(c_84, plain, (![A_17, B_18]: (k4_xboole_0(k4_xboole_0(A_17, B_18), A_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_76])).
% 2.80/1.43  tff(c_44, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.80/1.43  tff(c_42, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.80/1.43  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | k4_xboole_0(A_15, B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.80/1.43  tff(c_398, plain, (![B_94, A_95]: (B_94=A_95 | ~r1_tarski(A_95, B_94) | ~v1_zfmisc_1(B_94) | v1_xboole_0(B_94) | v1_xboole_0(A_95))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.80/1.43  tff(c_755, plain, (![B_123, A_124]: (B_123=A_124 | ~v1_zfmisc_1(B_123) | v1_xboole_0(B_123) | v1_xboole_0(A_124) | k4_xboole_0(A_124, B_123)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_398])).
% 2.80/1.43  tff(c_757, plain, (![A_124]: (A_124='#skF_4' | v1_xboole_0('#skF_4') | v1_xboole_0(A_124) | k4_xboole_0(A_124, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_755])).
% 2.80/1.43  tff(c_840, plain, (![A_131]: (A_131='#skF_4' | v1_xboole_0(A_131) | k4_xboole_0(A_131, '#skF_4')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_44, c_757])).
% 2.80/1.43  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.80/1.43  tff(c_52, plain, (![B_39, A_40]: (~v1_xboole_0(B_39) | B_39=A_40 | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.80/1.43  tff(c_55, plain, (![A_40]: (k1_xboole_0=A_40 | ~v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_6, c_52])).
% 2.80/1.43  tff(c_1263, plain, (![A_149]: (k1_xboole_0=A_149 | A_149='#skF_4' | k4_xboole_0(A_149, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_840, c_55])).
% 2.80/1.43  tff(c_1294, plain, (![B_150]: (k4_xboole_0('#skF_4', B_150)=k1_xboole_0 | k4_xboole_0('#skF_4', B_150)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_84, c_1263])).
% 2.80/1.43  tff(c_56, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | k4_xboole_0(A_41, B_42)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.80/1.43  tff(c_38, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.80/1.43  tff(c_60, plain, (k4_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_38])).
% 2.80/1.43  tff(c_1333, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1294, c_60])).
% 2.80/1.43  tff(c_1379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_370, c_1333])).
% 2.80/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.43  
% 2.80/1.43  Inference rules
% 2.80/1.43  ----------------------
% 2.80/1.43  #Ref     : 1
% 2.80/1.43  #Sup     : 316
% 2.80/1.43  #Fact    : 1
% 2.80/1.43  #Define  : 0
% 2.80/1.43  #Split   : 2
% 2.80/1.43  #Chain   : 0
% 2.80/1.43  #Close   : 0
% 2.80/1.43  
% 2.80/1.43  Ordering : KBO
% 2.80/1.43  
% 2.80/1.43  Simplification rules
% 2.80/1.43  ----------------------
% 2.80/1.43  #Subsume      : 66
% 2.80/1.43  #Demod        : 94
% 2.80/1.43  #Tautology    : 164
% 2.80/1.43  #SimpNegUnit  : 13
% 2.80/1.43  #BackRed      : 0
% 2.80/1.43  
% 2.80/1.43  #Partial instantiations: 0
% 2.80/1.43  #Strategies tried      : 1
% 2.80/1.43  
% 2.80/1.43  Timing (in seconds)
% 2.80/1.43  ----------------------
% 2.80/1.44  Preprocessing        : 0.30
% 2.80/1.44  Parsing              : 0.16
% 2.80/1.44  CNF conversion       : 0.02
% 2.80/1.44  Main loop            : 0.39
% 2.80/1.44  Inferencing          : 0.15
% 2.80/1.44  Reduction            : 0.11
% 2.80/1.44  Demodulation         : 0.07
% 2.80/1.44  BG Simplification    : 0.02
% 2.80/1.44  Subsumption          : 0.08
% 2.80/1.44  Abstraction          : 0.02
% 2.80/1.44  MUC search           : 0.00
% 2.80/1.44  Cooper               : 0.00
% 2.80/1.44  Total                : 0.71
% 2.80/1.44  Index Insertion      : 0.00
% 2.80/1.44  Index Deletion       : 0.00
% 2.80/1.44  Index Matching       : 0.00
% 2.80/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
