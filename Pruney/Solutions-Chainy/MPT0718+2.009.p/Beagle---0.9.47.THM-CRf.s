%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:42 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   49 (  69 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :  112 ( 214 expanded)
%              Number of equality atoms :    5 (  17 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v2_relat_1,type,(
    v2_relat_1: $i > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v5_funct_1(A,B)
                & k1_relat_1(A) = k1_relat_1(B) )
             => v2_relat_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_relat_1(A)
      <=> ! [B] :
            ~ ( r2_hidden(B,k1_relat_1(A))
              & v1_xboole_0(k1_funct_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_24,plain,(
    ~ v2_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_30,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    v5_funct_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    k1_relat_1('#skF_5') = k1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_81,plain,(
    ! [A_38] :
      ( r2_hidden('#skF_2'(A_38),k1_relat_1(A_38))
      | v2_relat_1(A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_84,plain,
    ( r2_hidden('#skF_2'('#skF_5'),k1_relat_1('#skF_4'))
    | v2_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_81])).

tff(c_86,plain,
    ( r2_hidden('#skF_2'('#skF_5'),k1_relat_1('#skF_4'))
    | v2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_84])).

tff(c_87,plain,(
    r2_hidden('#skF_2'('#skF_5'),k1_relat_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_86])).

tff(c_75,plain,(
    ! [A_37] :
      ( v1_xboole_0(k1_funct_1(A_37,'#skF_2'(A_37)))
      | v2_relat_1(A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_79,plain,(
    ! [A_37] :
      ( k1_funct_1(A_37,'#skF_2'(A_37)) = k1_xboole_0
      | v2_relat_1(A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(resolution,[status(thm)],[c_75,c_2])).

tff(c_164,plain,(
    ! [B_53,C_54,A_55] :
      ( r2_hidden(k1_funct_1(B_53,C_54),k1_funct_1(A_55,C_54))
      | ~ r2_hidden(C_54,k1_relat_1(B_53))
      | ~ v5_funct_1(B_53,A_55)
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_funct_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_174,plain,(
    ! [B_53,A_37] :
      ( r2_hidden(k1_funct_1(B_53,'#skF_2'(A_37)),k1_xboole_0)
      | ~ r2_hidden('#skF_2'(A_37),k1_relat_1(B_53))
      | ~ v5_funct_1(B_53,A_37)
      | ~ v1_funct_1(B_53)
      | ~ v1_relat_1(B_53)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37)
      | v2_relat_1(A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_164])).

tff(c_194,plain,(
    ! [B_59,A_60] :
      ( r2_hidden(k1_funct_1(B_59,'#skF_2'(A_60)),k1_xboole_0)
      | ~ r2_hidden('#skF_2'(A_60),k1_relat_1(B_59))
      | ~ v5_funct_1(B_59,A_60)
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59)
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60)
      | v2_relat_1(A_60)
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_164])).

tff(c_10,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_45,plain,(
    ! [A_29,B_30,C_31] :
      ( ~ r1_xboole_0(A_29,B_30)
      | ~ r2_hidden(C_31,B_30)
      | ~ r2_hidden(C_31,A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_48,plain,(
    ! [C_31,A_7] :
      ( ~ r2_hidden(C_31,k1_xboole_0)
      | ~ r2_hidden(C_31,A_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_45])).

tff(c_229,plain,(
    ! [B_67,A_68,A_69] :
      ( ~ r2_hidden(k1_funct_1(B_67,'#skF_2'(A_68)),A_69)
      | ~ r2_hidden('#skF_2'(A_68),k1_relat_1(B_67))
      | ~ v5_funct_1(B_67,A_68)
      | ~ v1_funct_1(B_67)
      | ~ v1_relat_1(B_67)
      | v2_relat_1(A_68)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_194,c_48])).

tff(c_243,plain,(
    ! [A_70,B_71] :
      ( ~ r2_hidden('#skF_2'(A_70),k1_relat_1(B_71))
      | ~ v5_funct_1(B_71,A_70)
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71)
      | v2_relat_1(A_70)
      | ~ v1_funct_1(A_70)
      | ~ v1_relat_1(A_70) ) ),
    inference(resolution,[status(thm)],[c_174,c_229])).

tff(c_246,plain,
    ( ~ v5_funct_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | v2_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_87,c_243])).

tff(c_255,plain,(
    v2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_36,c_34,c_28,c_246])).

tff(c_257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_255])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:57:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.25  
% 2.23/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.25  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1
% 2.23/1.25  
% 2.23/1.25  %Foreground sorts:
% 2.23/1.25  
% 2.23/1.25  
% 2.23/1.25  %Background operators:
% 2.23/1.25  
% 2.23/1.25  
% 2.23/1.25  %Foreground operators:
% 2.23/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.25  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.23/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.25  tff(v2_relat_1, type, v2_relat_1: $i > $o).
% 2.23/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.25  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.23/1.25  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.23/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.23/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.23/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.25  
% 2.23/1.27  tff(f_93, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v5_funct_1(A, B) & (k1_relat_1(A) = k1_relat_1(B))) => v2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_funct_1)).
% 2.23/1.27  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_relat_1(A) <=> (![B]: ~(r2_hidden(B, k1_relat_1(A)) & v1_xboole_0(k1_funct_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_funct_1)).
% 2.23/1.27  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.23/1.27  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 2.23/1.27  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.23/1.27  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.23/1.27  tff(c_24, plain, (~v2_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.27  tff(c_32, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.27  tff(c_30, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.27  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.27  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.27  tff(c_28, plain, (v5_funct_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.27  tff(c_26, plain, (k1_relat_1('#skF_5')=k1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.23/1.27  tff(c_81, plain, (![A_38]: (r2_hidden('#skF_2'(A_38), k1_relat_1(A_38)) | v2_relat_1(A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.23/1.27  tff(c_84, plain, (r2_hidden('#skF_2'('#skF_5'), k1_relat_1('#skF_4')) | v2_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_26, c_81])).
% 2.23/1.27  tff(c_86, plain, (r2_hidden('#skF_2'('#skF_5'), k1_relat_1('#skF_4')) | v2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_84])).
% 2.23/1.27  tff(c_87, plain, (r2_hidden('#skF_2'('#skF_5'), k1_relat_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_24, c_86])).
% 2.23/1.27  tff(c_75, plain, (![A_37]: (v1_xboole_0(k1_funct_1(A_37, '#skF_2'(A_37))) | v2_relat_1(A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.23/1.27  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.27  tff(c_79, plain, (![A_37]: (k1_funct_1(A_37, '#skF_2'(A_37))=k1_xboole_0 | v2_relat_1(A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(resolution, [status(thm)], [c_75, c_2])).
% 2.23/1.27  tff(c_164, plain, (![B_53, C_54, A_55]: (r2_hidden(k1_funct_1(B_53, C_54), k1_funct_1(A_55, C_54)) | ~r2_hidden(C_54, k1_relat_1(B_53)) | ~v5_funct_1(B_53, A_55) | ~v1_funct_1(B_53) | ~v1_relat_1(B_53) | ~v1_funct_1(A_55) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.23/1.27  tff(c_174, plain, (![B_53, A_37]: (r2_hidden(k1_funct_1(B_53, '#skF_2'(A_37)), k1_xboole_0) | ~r2_hidden('#skF_2'(A_37), k1_relat_1(B_53)) | ~v5_funct_1(B_53, A_37) | ~v1_funct_1(B_53) | ~v1_relat_1(B_53) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37) | v2_relat_1(A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(superposition, [status(thm), theory('equality')], [c_79, c_164])).
% 2.23/1.27  tff(c_194, plain, (![B_59, A_60]: (r2_hidden(k1_funct_1(B_59, '#skF_2'(A_60)), k1_xboole_0) | ~r2_hidden('#skF_2'(A_60), k1_relat_1(B_59)) | ~v5_funct_1(B_59, A_60) | ~v1_funct_1(B_59) | ~v1_relat_1(B_59) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60) | v2_relat_1(A_60) | ~v1_funct_1(A_60) | ~v1_relat_1(A_60))), inference(superposition, [status(thm), theory('equality')], [c_79, c_164])).
% 2.23/1.27  tff(c_10, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.23/1.27  tff(c_45, plain, (![A_29, B_30, C_31]: (~r1_xboole_0(A_29, B_30) | ~r2_hidden(C_31, B_30) | ~r2_hidden(C_31, A_29))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.23/1.27  tff(c_48, plain, (![C_31, A_7]: (~r2_hidden(C_31, k1_xboole_0) | ~r2_hidden(C_31, A_7))), inference(resolution, [status(thm)], [c_10, c_45])).
% 2.23/1.27  tff(c_229, plain, (![B_67, A_68, A_69]: (~r2_hidden(k1_funct_1(B_67, '#skF_2'(A_68)), A_69) | ~r2_hidden('#skF_2'(A_68), k1_relat_1(B_67)) | ~v5_funct_1(B_67, A_68) | ~v1_funct_1(B_67) | ~v1_relat_1(B_67) | v2_relat_1(A_68) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(resolution, [status(thm)], [c_194, c_48])).
% 2.23/1.27  tff(c_243, plain, (![A_70, B_71]: (~r2_hidden('#skF_2'(A_70), k1_relat_1(B_71)) | ~v5_funct_1(B_71, A_70) | ~v1_funct_1(B_71) | ~v1_relat_1(B_71) | v2_relat_1(A_70) | ~v1_funct_1(A_70) | ~v1_relat_1(A_70))), inference(resolution, [status(thm)], [c_174, c_229])).
% 2.23/1.27  tff(c_246, plain, (~v5_funct_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | v2_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_87, c_243])).
% 2.23/1.27  tff(c_255, plain, (v2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_36, c_34, c_28, c_246])).
% 2.23/1.27  tff(c_257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_255])).
% 2.23/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.27  
% 2.23/1.27  Inference rules
% 2.23/1.27  ----------------------
% 2.23/1.27  #Ref     : 0
% 2.23/1.27  #Sup     : 43
% 2.23/1.27  #Fact    : 0
% 2.23/1.27  #Define  : 0
% 2.23/1.27  #Split   : 4
% 2.23/1.27  #Chain   : 0
% 2.23/1.27  #Close   : 0
% 2.23/1.27  
% 2.23/1.27  Ordering : KBO
% 2.23/1.27  
% 2.23/1.27  Simplification rules
% 2.23/1.27  ----------------------
% 2.23/1.27  #Subsume      : 10
% 2.23/1.27  #Demod        : 33
% 2.23/1.27  #Tautology    : 10
% 2.23/1.27  #SimpNegUnit  : 8
% 2.23/1.27  #BackRed      : 3
% 2.23/1.27  
% 2.23/1.27  #Partial instantiations: 0
% 2.23/1.27  #Strategies tried      : 1
% 2.23/1.27  
% 2.23/1.27  Timing (in seconds)
% 2.23/1.27  ----------------------
% 2.23/1.27  Preprocessing        : 0.28
% 2.23/1.27  Parsing              : 0.15
% 2.23/1.27  CNF conversion       : 0.02
% 2.23/1.27  Main loop            : 0.23
% 2.23/1.27  Inferencing          : 0.10
% 2.23/1.27  Reduction            : 0.06
% 2.23/1.27  Demodulation         : 0.05
% 2.23/1.27  BG Simplification    : 0.02
% 2.23/1.27  Subsumption          : 0.04
% 2.23/1.27  Abstraction          : 0.01
% 2.23/1.27  MUC search           : 0.00
% 2.23/1.27  Cooper               : 0.00
% 2.23/1.27  Total                : 0.54
% 2.23/1.27  Index Insertion      : 0.00
% 2.23/1.27  Index Deletion       : 0.00
% 2.23/1.27  Index Matching       : 0.00
% 2.23/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
