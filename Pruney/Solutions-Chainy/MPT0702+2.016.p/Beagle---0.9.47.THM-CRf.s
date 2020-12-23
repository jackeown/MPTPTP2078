%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:04 EST 2020

% Result     : Theorem 6.21s
% Output     : CNFRefutation 6.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 115 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :   17
%              Number of atoms          :  144 ( 344 expanded)
%              Number of equality atoms :    7 (  16 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

tff(c_38,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_48,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    v2_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_42,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,k10_relat_1(B_23,k9_relat_1(B_23,A_22)))
      | ~ r1_tarski(A_22,k1_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_90,plain,(
    ! [B_41,A_42] :
      ( r1_tarski(k10_relat_1(B_41,k9_relat_1(B_41,A_42)),A_42)
      | ~ v2_funct_1(B_41)
      | ~ v1_funct_1(B_41)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_720,plain,(
    ! [B_137,A_138] :
      ( k10_relat_1(B_137,k9_relat_1(B_137,A_138)) = A_138
      | ~ r1_tarski(A_138,k10_relat_1(B_137,k9_relat_1(B_137,A_138)))
      | ~ v2_funct_1(B_137)
      | ~ v1_funct_1(B_137)
      | ~ v1_relat_1(B_137) ) ),
    inference(resolution,[status(thm)],[c_90,c_8])).

tff(c_740,plain,(
    ! [B_139,A_140] :
      ( k10_relat_1(B_139,k9_relat_1(B_139,A_140)) = A_140
      | ~ v2_funct_1(B_139)
      | ~ v1_funct_1(B_139)
      | ~ r1_tarski(A_140,k1_relat_1(B_139))
      | ~ v1_relat_1(B_139) ) ),
    inference(resolution,[status(thm)],[c_34,c_720])).

tff(c_752,plain,
    ( k10_relat_1('#skF_6',k9_relat_1('#skF_6','#skF_4')) = '#skF_4'
    | ~ v2_funct_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_740])).

tff(c_764,plain,(
    k10_relat_1('#skF_6',k9_relat_1('#skF_6','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_752])).

tff(c_20,plain,(
    ! [D_21,A_10,B_17] :
      ( r2_hidden(D_21,k1_relat_1(A_10))
      | ~ r2_hidden(D_21,k10_relat_1(A_10,B_17))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_802,plain,(
    ! [D_21] :
      ( r2_hidden(D_21,k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_21,'#skF_4')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_764,c_20])).

tff(c_830,plain,(
    ! [D_21] :
      ( r2_hidden(D_21,k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_21,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_802])).

tff(c_36,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k10_relat_1(B_25,k9_relat_1(B_25,A_24)),A_24)
      | ~ v2_funct_1(B_25)
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_44,plain,(
    r1_tarski(k9_relat_1('#skF_6','#skF_4'),k9_relat_1('#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_148,plain,(
    ! [A_51,D_52,B_53] :
      ( r2_hidden(k1_funct_1(A_51,D_52),B_53)
      | ~ r2_hidden(D_52,k10_relat_1(A_51,B_53))
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_336,plain,(
    ! [A_87,D_88,B_89,B_90] :
      ( r2_hidden(k1_funct_1(A_87,D_88),B_89)
      | ~ r1_tarski(B_90,B_89)
      | ~ r2_hidden(D_88,k10_relat_1(A_87,B_90))
      | ~ v1_funct_1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(resolution,[status(thm)],[c_148,c_2])).

tff(c_390,plain,(
    ! [A_98,D_99] :
      ( r2_hidden(k1_funct_1(A_98,D_99),k9_relat_1('#skF_6','#skF_5'))
      | ~ r2_hidden(D_99,k10_relat_1(A_98,k9_relat_1('#skF_6','#skF_4')))
      | ~ v1_funct_1(A_98)
      | ~ v1_relat_1(A_98) ) ),
    inference(resolution,[status(thm)],[c_44,c_336])).

tff(c_887,plain,(
    ! [A_146,D_147,B_148] :
      ( r2_hidden(k1_funct_1(A_146,D_147),B_148)
      | ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),B_148)
      | ~ r2_hidden(D_147,k10_relat_1(A_146,k9_relat_1('#skF_6','#skF_4')))
      | ~ v1_funct_1(A_146)
      | ~ v1_relat_1(A_146) ) ),
    inference(resolution,[status(thm)],[c_390,c_2])).

tff(c_889,plain,(
    ! [D_147,B_148] :
      ( r2_hidden(k1_funct_1('#skF_6',D_147),B_148)
      | ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),B_148)
      | ~ r2_hidden(D_147,'#skF_4')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_764,c_887])).

tff(c_1321,plain,(
    ! [D_166,B_167] :
      ( r2_hidden(k1_funct_1('#skF_6',D_166),B_167)
      | ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),B_167)
      | ~ r2_hidden(D_166,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_889])).

tff(c_16,plain,(
    ! [D_21,A_10,B_17] :
      ( r2_hidden(D_21,k10_relat_1(A_10,B_17))
      | ~ r2_hidden(k1_funct_1(A_10,D_21),B_17)
      | ~ r2_hidden(D_21,k1_relat_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1336,plain,(
    ! [D_166,B_167] :
      ( r2_hidden(D_166,k10_relat_1('#skF_6',B_167))
      | ~ r2_hidden(D_166,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),B_167)
      | ~ r2_hidden(D_166,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1321,c_16])).

tff(c_2038,plain,(
    ! [D_199,B_200] :
      ( r2_hidden(D_199,k10_relat_1('#skF_6',B_200))
      | ~ r2_hidden(D_199,k1_relat_1('#skF_6'))
      | ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),B_200)
      | ~ r2_hidden(D_199,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1336])).

tff(c_3574,plain,(
    ! [D_282,B_283,B_284] :
      ( r2_hidden(D_282,B_283)
      | ~ r1_tarski(k10_relat_1('#skF_6',B_284),B_283)
      | ~ r2_hidden(D_282,k1_relat_1('#skF_6'))
      | ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),B_284)
      | ~ r2_hidden(D_282,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2038,c_2])).

tff(c_3613,plain,(
    ! [D_282,A_24] :
      ( r2_hidden(D_282,A_24)
      | ~ r2_hidden(D_282,k1_relat_1('#skF_6'))
      | ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k9_relat_1('#skF_6',A_24))
      | ~ r2_hidden(D_282,'#skF_4')
      | ~ v2_funct_1('#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_36,c_3574])).

tff(c_3691,plain,(
    ! [D_289,A_290] :
      ( r2_hidden(D_289,A_290)
      | ~ r2_hidden(D_289,k1_relat_1('#skF_6'))
      | ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k9_relat_1('#skF_6',A_290))
      | ~ r2_hidden(D_289,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_40,c_3613])).

tff(c_3834,plain,(
    ! [D_291,A_292] :
      ( r2_hidden(D_291,A_292)
      | ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k9_relat_1('#skF_6',A_292))
      | ~ r2_hidden(D_291,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_830,c_3691])).

tff(c_3843,plain,(
    ! [D_293] :
      ( r2_hidden(D_293,'#skF_5')
      | ~ r2_hidden(D_293,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12,c_3834])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3877,plain,(
    ! [A_294] :
      ( r1_tarski(A_294,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_294,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3843,c_4])).

tff(c_3903,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_3877])).

tff(c_3913,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_3903])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:24:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.21/2.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.21/2.18  
% 6.21/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.21/2.19  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k1_funct_1 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 6.21/2.19  
% 6.21/2.19  %Foreground sorts:
% 6.21/2.19  
% 6.21/2.19  
% 6.21/2.19  %Background operators:
% 6.21/2.19  
% 6.21/2.19  
% 6.21/2.19  %Foreground operators:
% 6.21/2.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.21/2.19  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.21/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.21/2.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.21/2.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.21/2.19  tff('#skF_5', type, '#skF_5': $i).
% 6.21/2.19  tff('#skF_6', type, '#skF_6': $i).
% 6.21/2.19  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.21/2.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.21/2.19  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.21/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.21/2.19  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.21/2.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.21/2.19  tff('#skF_4', type, '#skF_4': $i).
% 6.21/2.19  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.21/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.21/2.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.21/2.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.21/2.19  
% 6.21/2.20  tff(f_83, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 6.21/2.20  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.21/2.20  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.21/2.20  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 6.21/2.20  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 6.21/2.20  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, k1_relat_1(A)) & r2_hidden(k1_funct_1(A, D), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_funct_1)).
% 6.21/2.20  tff(c_38, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.21/2.20  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.21/2.20  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.21/2.20  tff(c_48, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.21/2.20  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.21/2.20  tff(c_40, plain, (v2_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.21/2.20  tff(c_42, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.21/2.20  tff(c_34, plain, (![A_22, B_23]: (r1_tarski(A_22, k10_relat_1(B_23, k9_relat_1(B_23, A_22))) | ~r1_tarski(A_22, k1_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.21/2.20  tff(c_90, plain, (![B_41, A_42]: (r1_tarski(k10_relat_1(B_41, k9_relat_1(B_41, A_42)), A_42) | ~v2_funct_1(B_41) | ~v1_funct_1(B_41) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.21/2.20  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.21/2.20  tff(c_720, plain, (![B_137, A_138]: (k10_relat_1(B_137, k9_relat_1(B_137, A_138))=A_138 | ~r1_tarski(A_138, k10_relat_1(B_137, k9_relat_1(B_137, A_138))) | ~v2_funct_1(B_137) | ~v1_funct_1(B_137) | ~v1_relat_1(B_137))), inference(resolution, [status(thm)], [c_90, c_8])).
% 6.21/2.20  tff(c_740, plain, (![B_139, A_140]: (k10_relat_1(B_139, k9_relat_1(B_139, A_140))=A_140 | ~v2_funct_1(B_139) | ~v1_funct_1(B_139) | ~r1_tarski(A_140, k1_relat_1(B_139)) | ~v1_relat_1(B_139))), inference(resolution, [status(thm)], [c_34, c_720])).
% 6.21/2.20  tff(c_752, plain, (k10_relat_1('#skF_6', k9_relat_1('#skF_6', '#skF_4'))='#skF_4' | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_740])).
% 6.21/2.20  tff(c_764, plain, (k10_relat_1('#skF_6', k9_relat_1('#skF_6', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_752])).
% 6.21/2.20  tff(c_20, plain, (![D_21, A_10, B_17]: (r2_hidden(D_21, k1_relat_1(A_10)) | ~r2_hidden(D_21, k10_relat_1(A_10, B_17)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.21/2.20  tff(c_802, plain, (![D_21]: (r2_hidden(D_21, k1_relat_1('#skF_6')) | ~r2_hidden(D_21, '#skF_4') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_764, c_20])).
% 6.21/2.20  tff(c_830, plain, (![D_21]: (r2_hidden(D_21, k1_relat_1('#skF_6')) | ~r2_hidden(D_21, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_802])).
% 6.21/2.20  tff(c_36, plain, (![B_25, A_24]: (r1_tarski(k10_relat_1(B_25, k9_relat_1(B_25, A_24)), A_24) | ~v2_funct_1(B_25) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.21/2.20  tff(c_44, plain, (r1_tarski(k9_relat_1('#skF_6', '#skF_4'), k9_relat_1('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.21/2.20  tff(c_148, plain, (![A_51, D_52, B_53]: (r2_hidden(k1_funct_1(A_51, D_52), B_53) | ~r2_hidden(D_52, k10_relat_1(A_51, B_53)) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.21/2.20  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.21/2.20  tff(c_336, plain, (![A_87, D_88, B_89, B_90]: (r2_hidden(k1_funct_1(A_87, D_88), B_89) | ~r1_tarski(B_90, B_89) | ~r2_hidden(D_88, k10_relat_1(A_87, B_90)) | ~v1_funct_1(A_87) | ~v1_relat_1(A_87))), inference(resolution, [status(thm)], [c_148, c_2])).
% 6.21/2.20  tff(c_390, plain, (![A_98, D_99]: (r2_hidden(k1_funct_1(A_98, D_99), k9_relat_1('#skF_6', '#skF_5')) | ~r2_hidden(D_99, k10_relat_1(A_98, k9_relat_1('#skF_6', '#skF_4'))) | ~v1_funct_1(A_98) | ~v1_relat_1(A_98))), inference(resolution, [status(thm)], [c_44, c_336])).
% 6.21/2.20  tff(c_887, plain, (![A_146, D_147, B_148]: (r2_hidden(k1_funct_1(A_146, D_147), B_148) | ~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), B_148) | ~r2_hidden(D_147, k10_relat_1(A_146, k9_relat_1('#skF_6', '#skF_4'))) | ~v1_funct_1(A_146) | ~v1_relat_1(A_146))), inference(resolution, [status(thm)], [c_390, c_2])).
% 6.21/2.20  tff(c_889, plain, (![D_147, B_148]: (r2_hidden(k1_funct_1('#skF_6', D_147), B_148) | ~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), B_148) | ~r2_hidden(D_147, '#skF_4') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_764, c_887])).
% 6.21/2.20  tff(c_1321, plain, (![D_166, B_167]: (r2_hidden(k1_funct_1('#skF_6', D_166), B_167) | ~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), B_167) | ~r2_hidden(D_166, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_889])).
% 6.21/2.20  tff(c_16, plain, (![D_21, A_10, B_17]: (r2_hidden(D_21, k10_relat_1(A_10, B_17)) | ~r2_hidden(k1_funct_1(A_10, D_21), B_17) | ~r2_hidden(D_21, k1_relat_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.21/2.20  tff(c_1336, plain, (![D_166, B_167]: (r2_hidden(D_166, k10_relat_1('#skF_6', B_167)) | ~r2_hidden(D_166, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), B_167) | ~r2_hidden(D_166, '#skF_4'))), inference(resolution, [status(thm)], [c_1321, c_16])).
% 6.21/2.20  tff(c_2038, plain, (![D_199, B_200]: (r2_hidden(D_199, k10_relat_1('#skF_6', B_200)) | ~r2_hidden(D_199, k1_relat_1('#skF_6')) | ~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), B_200) | ~r2_hidden(D_199, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1336])).
% 6.21/2.20  tff(c_3574, plain, (![D_282, B_283, B_284]: (r2_hidden(D_282, B_283) | ~r1_tarski(k10_relat_1('#skF_6', B_284), B_283) | ~r2_hidden(D_282, k1_relat_1('#skF_6')) | ~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), B_284) | ~r2_hidden(D_282, '#skF_4'))), inference(resolution, [status(thm)], [c_2038, c_2])).
% 6.21/2.20  tff(c_3613, plain, (![D_282, A_24]: (r2_hidden(D_282, A_24) | ~r2_hidden(D_282, k1_relat_1('#skF_6')) | ~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k9_relat_1('#skF_6', A_24)) | ~r2_hidden(D_282, '#skF_4') | ~v2_funct_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_36, c_3574])).
% 6.21/2.20  tff(c_3691, plain, (![D_289, A_290]: (r2_hidden(D_289, A_290) | ~r2_hidden(D_289, k1_relat_1('#skF_6')) | ~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k9_relat_1('#skF_6', A_290)) | ~r2_hidden(D_289, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_40, c_3613])).
% 6.21/2.20  tff(c_3834, plain, (![D_291, A_292]: (r2_hidden(D_291, A_292) | ~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k9_relat_1('#skF_6', A_292)) | ~r2_hidden(D_291, '#skF_4'))), inference(resolution, [status(thm)], [c_830, c_3691])).
% 6.21/2.20  tff(c_3843, plain, (![D_293]: (r2_hidden(D_293, '#skF_5') | ~r2_hidden(D_293, '#skF_4'))), inference(resolution, [status(thm)], [c_12, c_3834])).
% 6.21/2.20  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.21/2.20  tff(c_3877, plain, (![A_294]: (r1_tarski(A_294, '#skF_5') | ~r2_hidden('#skF_1'(A_294, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_3843, c_4])).
% 6.21/2.20  tff(c_3903, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_3877])).
% 6.21/2.20  tff(c_3913, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_3903])).
% 6.21/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.21/2.20  
% 6.21/2.20  Inference rules
% 6.21/2.20  ----------------------
% 6.21/2.20  #Ref     : 0
% 6.21/2.20  #Sup     : 933
% 6.21/2.20  #Fact    : 0
% 6.21/2.20  #Define  : 0
% 6.21/2.20  #Split   : 9
% 6.21/2.20  #Chain   : 0
% 6.21/2.20  #Close   : 0
% 6.21/2.20  
% 6.21/2.20  Ordering : KBO
% 6.21/2.20  
% 6.21/2.20  Simplification rules
% 6.21/2.20  ----------------------
% 6.21/2.20  #Subsume      : 327
% 6.21/2.20  #Demod        : 298
% 6.21/2.20  #Tautology    : 52
% 6.21/2.20  #SimpNegUnit  : 2
% 6.21/2.20  #BackRed      : 0
% 6.21/2.20  
% 6.21/2.20  #Partial instantiations: 0
% 6.21/2.20  #Strategies tried      : 1
% 6.21/2.20  
% 6.21/2.20  Timing (in seconds)
% 6.21/2.20  ----------------------
% 6.21/2.20  Preprocessing        : 0.29
% 6.21/2.20  Parsing              : 0.16
% 6.21/2.20  CNF conversion       : 0.02
% 6.21/2.20  Main loop            : 1.15
% 6.21/2.20  Inferencing          : 0.34
% 6.21/2.20  Reduction            : 0.29
% 6.21/2.20  Demodulation         : 0.19
% 6.21/2.20  BG Simplification    : 0.05
% 6.21/2.20  Subsumption          : 0.41
% 6.21/2.20  Abstraction          : 0.05
% 6.21/2.20  MUC search           : 0.00
% 6.21/2.20  Cooper               : 0.00
% 6.21/2.20  Total                : 1.47
% 6.21/2.20  Index Insertion      : 0.00
% 6.21/2.20  Index Deletion       : 0.00
% 6.21/2.20  Index Matching       : 0.00
% 6.21/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
