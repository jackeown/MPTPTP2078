%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:45 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   52 (  57 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 (  86 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k4_tarski > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_74,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_83,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_43,axiom,(
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

tff(f_73,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36,plain,(
    ! [A_57] : v1_relat_1(k6_relat_1(A_57)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_50,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_36])).

tff(c_303,plain,(
    ! [A_114,B_115,C_116] :
      ( r2_hidden('#skF_4'(A_114,B_115,C_116),B_115)
      | r2_hidden('#skF_5'(A_114,B_115,C_116),C_116)
      | k9_relat_1(A_114,B_115) = C_116
      | ~ v1_relat_1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_85,plain,(
    ! [A_73,B_74] :
      ( r2_hidden('#skF_2'(A_73,B_74),B_74)
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    ! [B_59,A_58] :
      ( ~ r1_tarski(B_59,A_58)
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_119,plain,(
    ! [B_86,A_87] :
      ( ~ r1_tarski(B_86,'#skF_2'(A_87,B_86))
      | ~ r2_hidden(A_87,B_86) ) ),
    inference(resolution,[status(thm)],[c_85,c_40])).

tff(c_124,plain,(
    ! [A_87] : ~ r2_hidden(A_87,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_119])).

tff(c_354,plain,(
    ! [A_114,C_116] :
      ( r2_hidden('#skF_5'(A_114,k1_xboole_0,C_116),C_116)
      | k9_relat_1(A_114,k1_xboole_0) = C_116
      | ~ v1_relat_1(A_114) ) ),
    inference(resolution,[status(thm)],[c_303,c_124])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_153,plain,(
    ! [D_92,A_93,B_94] :
      ( ~ r2_hidden(D_92,'#skF_2'(A_93,B_94))
      | ~ r2_hidden(D_92,B_94)
      | ~ r2_hidden(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_573,plain,(
    ! [A_137,B_138,B_139] :
      ( ~ r2_hidden('#skF_1'('#skF_2'(A_137,B_138),B_139),B_138)
      | ~ r2_hidden(A_137,B_138)
      | r1_xboole_0('#skF_2'(A_137,B_138),B_139) ) ),
    inference(resolution,[status(thm)],[c_6,c_153])).

tff(c_579,plain,(
    ! [A_140,B_141] :
      ( ~ r2_hidden(A_140,B_141)
      | r1_xboole_0('#skF_2'(A_140,B_141),B_141) ) ),
    inference(resolution,[status(thm)],[c_4,c_573])).

tff(c_42,plain,(
    ! [B_61] :
      ( ~ r1_xboole_0(B_61,'#skF_7')
      | ~ r2_hidden(B_61,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_93,plain,(
    ! [A_73] :
      ( ~ r1_xboole_0('#skF_2'(A_73,'#skF_7'),'#skF_7')
      | ~ r2_hidden(A_73,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_85,c_42])).

tff(c_595,plain,(
    ! [A_144] : ~ r2_hidden(A_144,'#skF_7') ),
    inference(resolution,[status(thm)],[c_579,c_93])).

tff(c_648,plain,(
    ! [A_147] :
      ( k9_relat_1(A_147,k1_xboole_0) = '#skF_7'
      | ~ v1_relat_1(A_147) ) ),
    inference(resolution,[status(thm)],[c_354,c_595])).

tff(c_655,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_50,c_648])).

tff(c_32,plain,(
    ! [A_56] : k9_relat_1(k1_xboole_0,A_56) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_683,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_655,c_32])).

tff(c_706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_683])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.53  
% 3.05/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.53  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k4_tarski > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 3.05/1.53  
% 3.05/1.53  %Foreground sorts:
% 3.05/1.53  
% 3.05/1.53  
% 3.05/1.53  %Background operators:
% 3.05/1.53  
% 3.05/1.53  
% 3.05/1.53  %Foreground operators:
% 3.05/1.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.05/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.05/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.05/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.05/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.05/1.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.05/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.05/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.05/1.53  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.05/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.05/1.53  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.05/1.53  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 3.05/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.05/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.05/1.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.05/1.53  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.05/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.05/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.05/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.05/1.53  
% 3.05/1.54  tff(f_94, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 3.05/1.54  tff(f_74, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 3.05/1.54  tff(f_78, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.05/1.54  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 3.05/1.54  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.05/1.54  tff(f_58, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 3.05/1.54  tff(f_83, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.05/1.54  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.05/1.54  tff(f_73, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 3.05/1.54  tff(c_44, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.05/1.54  tff(c_34, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.05/1.54  tff(c_36, plain, (![A_57]: (v1_relat_1(k6_relat_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.05/1.54  tff(c_50, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_36])).
% 3.05/1.54  tff(c_303, plain, (![A_114, B_115, C_116]: (r2_hidden('#skF_4'(A_114, B_115, C_116), B_115) | r2_hidden('#skF_5'(A_114, B_115, C_116), C_116) | k9_relat_1(A_114, B_115)=C_116 | ~v1_relat_1(A_114))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.05/1.54  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.05/1.54  tff(c_85, plain, (![A_73, B_74]: (r2_hidden('#skF_2'(A_73, B_74), B_74) | ~r2_hidden(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.05/1.54  tff(c_40, plain, (![B_59, A_58]: (~r1_tarski(B_59, A_58) | ~r2_hidden(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.05/1.54  tff(c_119, plain, (![B_86, A_87]: (~r1_tarski(B_86, '#skF_2'(A_87, B_86)) | ~r2_hidden(A_87, B_86))), inference(resolution, [status(thm)], [c_85, c_40])).
% 3.05/1.54  tff(c_124, plain, (![A_87]: (~r2_hidden(A_87, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_119])).
% 3.05/1.54  tff(c_354, plain, (![A_114, C_116]: (r2_hidden('#skF_5'(A_114, k1_xboole_0, C_116), C_116) | k9_relat_1(A_114, k1_xboole_0)=C_116 | ~v1_relat_1(A_114))), inference(resolution, [status(thm)], [c_303, c_124])).
% 3.05/1.54  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.05/1.54  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.05/1.54  tff(c_153, plain, (![D_92, A_93, B_94]: (~r2_hidden(D_92, '#skF_2'(A_93, B_94)) | ~r2_hidden(D_92, B_94) | ~r2_hidden(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.05/1.54  tff(c_573, plain, (![A_137, B_138, B_139]: (~r2_hidden('#skF_1'('#skF_2'(A_137, B_138), B_139), B_138) | ~r2_hidden(A_137, B_138) | r1_xboole_0('#skF_2'(A_137, B_138), B_139))), inference(resolution, [status(thm)], [c_6, c_153])).
% 3.05/1.54  tff(c_579, plain, (![A_140, B_141]: (~r2_hidden(A_140, B_141) | r1_xboole_0('#skF_2'(A_140, B_141), B_141))), inference(resolution, [status(thm)], [c_4, c_573])).
% 3.05/1.54  tff(c_42, plain, (![B_61]: (~r1_xboole_0(B_61, '#skF_7') | ~r2_hidden(B_61, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.05/1.54  tff(c_93, plain, (![A_73]: (~r1_xboole_0('#skF_2'(A_73, '#skF_7'), '#skF_7') | ~r2_hidden(A_73, '#skF_7'))), inference(resolution, [status(thm)], [c_85, c_42])).
% 3.05/1.54  tff(c_595, plain, (![A_144]: (~r2_hidden(A_144, '#skF_7'))), inference(resolution, [status(thm)], [c_579, c_93])).
% 3.05/1.54  tff(c_648, plain, (![A_147]: (k9_relat_1(A_147, k1_xboole_0)='#skF_7' | ~v1_relat_1(A_147))), inference(resolution, [status(thm)], [c_354, c_595])).
% 3.05/1.54  tff(c_655, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)='#skF_7'), inference(resolution, [status(thm)], [c_50, c_648])).
% 3.05/1.54  tff(c_32, plain, (![A_56]: (k9_relat_1(k1_xboole_0, A_56)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.05/1.54  tff(c_683, plain, (k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_655, c_32])).
% 3.05/1.54  tff(c_706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_683])).
% 3.05/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.54  
% 3.05/1.54  Inference rules
% 3.05/1.54  ----------------------
% 3.05/1.54  #Ref     : 0
% 3.05/1.54  #Sup     : 136
% 3.05/1.54  #Fact    : 0
% 3.05/1.54  #Define  : 0
% 3.05/1.54  #Split   : 0
% 3.05/1.54  #Chain   : 0
% 3.05/1.54  #Close   : 0
% 3.05/1.54  
% 3.05/1.54  Ordering : KBO
% 3.05/1.54  
% 3.05/1.54  Simplification rules
% 3.05/1.54  ----------------------
% 3.05/1.54  #Subsume      : 44
% 3.05/1.54  #Demod        : 57
% 3.05/1.54  #Tautology    : 27
% 3.05/1.54  #SimpNegUnit  : 3
% 3.05/1.54  #BackRed      : 2
% 3.05/1.54  
% 3.05/1.54  #Partial instantiations: 0
% 3.05/1.54  #Strategies tried      : 1
% 3.05/1.54  
% 3.05/1.54  Timing (in seconds)
% 3.05/1.54  ----------------------
% 3.05/1.55  Preprocessing        : 0.31
% 3.05/1.55  Parsing              : 0.16
% 3.05/1.55  CNF conversion       : 0.03
% 3.05/1.55  Main loop            : 0.46
% 3.05/1.55  Inferencing          : 0.18
% 3.05/1.55  Reduction            : 0.12
% 3.05/1.55  Demodulation         : 0.09
% 3.05/1.55  BG Simplification    : 0.02
% 3.05/1.55  Subsumption          : 0.09
% 3.05/1.55  Abstraction          : 0.02
% 3.05/1.55  MUC search           : 0.00
% 3.05/1.55  Cooper               : 0.00
% 3.05/1.55  Total                : 0.80
% 3.05/1.55  Index Insertion      : 0.00
% 3.05/1.55  Index Deletion       : 0.00
% 3.05/1.55  Index Matching       : 0.00
% 3.05/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
