%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:42 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   59 (  70 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 111 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
       => ( r1_xboole_0(B,C)
         => k5_relset_1(C,A,D,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_75,plain,(
    ! [A_44,B_45,C_46] :
      ( ~ r1_xboole_0(A_44,B_45)
      | ~ r2_hidden(C_46,B_45)
      | ~ r2_hidden(C_46,A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_89,plain,(
    ! [C_50] :
      ( ~ r2_hidden(C_50,'#skF_4')
      | ~ r2_hidden(C_50,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_75])).

tff(c_119,plain,(
    ! [A_54] :
      ( ~ r2_hidden('#skF_1'(A_54,'#skF_3'),'#skF_4')
      | r1_xboole_0(A_54,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_8,c_89])).

tff(c_124,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_119])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_58,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_67,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_58])).

tff(c_151,plain,(
    ! [A_57,B_58,C_59,D_60] :
      ( ~ r1_xboole_0(A_57,B_58)
      | r1_xboole_0(k2_zfmisc_1(A_57,C_59),k2_zfmisc_1(B_58,D_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_238,plain,(
    ! [A_84,C_85,B_86,D_87] :
      ( k3_xboole_0(k2_zfmisc_1(A_84,C_85),k2_zfmisc_1(B_86,D_87)) = k1_xboole_0
      | ~ r1_xboole_0(A_84,B_86) ) ),
    inference(resolution,[status(thm)],[c_151,c_2])).

tff(c_33,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_37,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_33])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_82,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_xboole_0(A_47,C_48)
      | ~ r1_xboole_0(B_49,C_48)
      | ~ r1_tarski(A_47,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_217,plain,(
    ! [A_78,B_79,A_80] :
      ( r1_xboole_0(A_78,B_79)
      | ~ r1_tarski(A_78,A_80)
      | k3_xboole_0(A_80,B_79) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_220,plain,(
    ! [B_79] :
      ( r1_xboole_0('#skF_5',B_79)
      | k3_xboole_0(k2_zfmisc_1('#skF_4','#skF_2'),B_79) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_37,c_217])).

tff(c_260,plain,(
    ! [B_88,D_89] :
      ( r1_xboole_0('#skF_5',k2_zfmisc_1(B_88,D_89))
      | ~ r1_xboole_0('#skF_4',B_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_220])).

tff(c_271,plain,(
    ! [B_90,D_91] :
      ( k3_xboole_0('#skF_5',k2_zfmisc_1(B_90,D_91)) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_90) ) ),
    inference(resolution,[status(thm)],[c_260,c_2])).

tff(c_22,plain,(
    ! [B_18,A_17] :
      ( k3_xboole_0(B_18,k2_zfmisc_1(A_17,k2_relat_1(B_18))) = k7_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_278,plain,(
    ! [B_90] :
      ( k7_relat_1('#skF_5',B_90) = k1_xboole_0
      | ~ v1_relat_1('#skF_5')
      | ~ r1_xboole_0('#skF_4',B_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_22])).

tff(c_300,plain,(
    ! [B_96] :
      ( k7_relat_1('#skF_5',B_96) = k1_xboole_0
      | ~ r1_xboole_0('#skF_4',B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_278])).

tff(c_317,plain,(
    k7_relat_1('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_124,c_300])).

tff(c_292,plain,(
    ! [A_92,B_93,C_94,D_95] :
      ( k5_relset_1(A_92,B_93,C_94,D_95) = k7_relat_1(C_94,D_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_299,plain,(
    ! [D_95] : k5_relset_1('#skF_4','#skF_2','#skF_5',D_95) = k7_relat_1('#skF_5',D_95) ),
    inference(resolution,[status(thm)],[c_32,c_292])).

tff(c_28,plain,(
    k5_relset_1('#skF_4','#skF_2','#skF_5','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_324,plain,(
    k7_relat_1('#skF_5','#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_28])).

tff(c_327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:57:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.35  
% 2.23/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.36  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.23/1.36  
% 2.23/1.36  %Foreground sorts:
% 2.23/1.36  
% 2.23/1.36  
% 2.23/1.36  %Background operators:
% 2.23/1.36  
% 2.23/1.36  
% 2.23/1.36  %Foreground operators:
% 2.23/1.36  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.23/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.23/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.23/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.23/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.23/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.36  
% 2.23/1.37  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.23/1.37  tff(f_82, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_xboole_0(B, C) => (k5_relset_1(C, A, D, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relset_1)).
% 2.23/1.37  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.23/1.37  tff(f_59, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.23/1.37  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.23/1.37  tff(f_63, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.23/1.37  tff(f_53, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.23/1.37  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_relat_1)).
% 2.23/1.37  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.23/1.37  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.23/1.37  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.23/1.37  tff(c_30, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.23/1.37  tff(c_75, plain, (![A_44, B_45, C_46]: (~r1_xboole_0(A_44, B_45) | ~r2_hidden(C_46, B_45) | ~r2_hidden(C_46, A_44))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.23/1.37  tff(c_89, plain, (![C_50]: (~r2_hidden(C_50, '#skF_4') | ~r2_hidden(C_50, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_75])).
% 2.23/1.37  tff(c_119, plain, (![A_54]: (~r2_hidden('#skF_1'(A_54, '#skF_3'), '#skF_4') | r1_xboole_0(A_54, '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_89])).
% 2.23/1.37  tff(c_124, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_10, c_119])).
% 2.23/1.37  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.23/1.37  tff(c_58, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.23/1.37  tff(c_67, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_58])).
% 2.23/1.37  tff(c_151, plain, (![A_57, B_58, C_59, D_60]: (~r1_xboole_0(A_57, B_58) | r1_xboole_0(k2_zfmisc_1(A_57, C_59), k2_zfmisc_1(B_58, D_60)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.23/1.37  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.37  tff(c_238, plain, (![A_84, C_85, B_86, D_87]: (k3_xboole_0(k2_zfmisc_1(A_84, C_85), k2_zfmisc_1(B_86, D_87))=k1_xboole_0 | ~r1_xboole_0(A_84, B_86))), inference(resolution, [status(thm)], [c_151, c_2])).
% 2.23/1.37  tff(c_33, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.23/1.37  tff(c_37, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_33])).
% 2.23/1.37  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.37  tff(c_82, plain, (![A_47, C_48, B_49]: (r1_xboole_0(A_47, C_48) | ~r1_xboole_0(B_49, C_48) | ~r1_tarski(A_47, B_49))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.23/1.37  tff(c_217, plain, (![A_78, B_79, A_80]: (r1_xboole_0(A_78, B_79) | ~r1_tarski(A_78, A_80) | k3_xboole_0(A_80, B_79)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_82])).
% 2.23/1.37  tff(c_220, plain, (![B_79]: (r1_xboole_0('#skF_5', B_79) | k3_xboole_0(k2_zfmisc_1('#skF_4', '#skF_2'), B_79)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_37, c_217])).
% 2.23/1.37  tff(c_260, plain, (![B_88, D_89]: (r1_xboole_0('#skF_5', k2_zfmisc_1(B_88, D_89)) | ~r1_xboole_0('#skF_4', B_88))), inference(superposition, [status(thm), theory('equality')], [c_238, c_220])).
% 2.23/1.37  tff(c_271, plain, (![B_90, D_91]: (k3_xboole_0('#skF_5', k2_zfmisc_1(B_90, D_91))=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_90))), inference(resolution, [status(thm)], [c_260, c_2])).
% 2.23/1.37  tff(c_22, plain, (![B_18, A_17]: (k3_xboole_0(B_18, k2_zfmisc_1(A_17, k2_relat_1(B_18)))=k7_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.23/1.37  tff(c_278, plain, (![B_90]: (k7_relat_1('#skF_5', B_90)=k1_xboole_0 | ~v1_relat_1('#skF_5') | ~r1_xboole_0('#skF_4', B_90))), inference(superposition, [status(thm), theory('equality')], [c_271, c_22])).
% 2.23/1.37  tff(c_300, plain, (![B_96]: (k7_relat_1('#skF_5', B_96)=k1_xboole_0 | ~r1_xboole_0('#skF_4', B_96))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_278])).
% 2.23/1.37  tff(c_317, plain, (k7_relat_1('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_124, c_300])).
% 2.23/1.37  tff(c_292, plain, (![A_92, B_93, C_94, D_95]: (k5_relset_1(A_92, B_93, C_94, D_95)=k7_relat_1(C_94, D_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.23/1.37  tff(c_299, plain, (![D_95]: (k5_relset_1('#skF_4', '#skF_2', '#skF_5', D_95)=k7_relat_1('#skF_5', D_95))), inference(resolution, [status(thm)], [c_32, c_292])).
% 2.23/1.37  tff(c_28, plain, (k5_relset_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.23/1.37  tff(c_324, plain, (k7_relat_1('#skF_5', '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_299, c_28])).
% 2.23/1.37  tff(c_327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_317, c_324])).
% 2.23/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.37  
% 2.23/1.37  Inference rules
% 2.23/1.37  ----------------------
% 2.23/1.37  #Ref     : 0
% 2.23/1.37  #Sup     : 68
% 2.23/1.37  #Fact    : 0
% 2.23/1.37  #Define  : 0
% 2.23/1.37  #Split   : 3
% 2.23/1.37  #Chain   : 0
% 2.23/1.37  #Close   : 0
% 2.23/1.37  
% 2.23/1.37  Ordering : KBO
% 2.23/1.37  
% 2.23/1.37  Simplification rules
% 2.23/1.37  ----------------------
% 2.23/1.37  #Subsume      : 4
% 2.23/1.37  #Demod        : 6
% 2.23/1.37  #Tautology    : 16
% 2.23/1.37  #SimpNegUnit  : 0
% 2.23/1.37  #BackRed      : 1
% 2.23/1.37  
% 2.23/1.37  #Partial instantiations: 0
% 2.23/1.37  #Strategies tried      : 1
% 2.23/1.37  
% 2.23/1.37  Timing (in seconds)
% 2.23/1.37  ----------------------
% 2.48/1.37  Preprocessing        : 0.33
% 2.48/1.37  Parsing              : 0.18
% 2.48/1.37  CNF conversion       : 0.02
% 2.48/1.37  Main loop            : 0.23
% 2.48/1.37  Inferencing          : 0.09
% 2.48/1.37  Reduction            : 0.05
% 2.48/1.37  Demodulation         : 0.04
% 2.48/1.37  BG Simplification    : 0.01
% 2.48/1.37  Subsumption          : 0.05
% 2.48/1.37  Abstraction          : 0.01
% 2.48/1.37  MUC search           : 0.00
% 2.48/1.37  Cooper               : 0.00
% 2.48/1.37  Total                : 0.59
% 2.48/1.37  Index Insertion      : 0.00
% 2.48/1.37  Index Deletion       : 0.00
% 2.48/1.37  Index Matching       : 0.00
% 2.48/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
