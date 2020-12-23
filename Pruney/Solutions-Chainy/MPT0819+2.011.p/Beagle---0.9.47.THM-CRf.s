%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:59 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 118 expanded)
%              Number of leaves         :   26 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :   92 ( 235 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( ( r1_tarski(A,B)
            & r1_tarski(C,D) )
         => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    ! [B_26,A_27] :
      ( v1_relat_1(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_35,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_32])).

tff(c_38,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_35])).

tff(c_94,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_98,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_94])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(B_8),A_7)
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_46,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_tarski(A_34,C_35)
      | ~ r1_tarski(B_36,C_35)
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_55,plain,(
    ! [A_34] :
      ( r1_tarski(A_34,'#skF_2')
      | ~ r1_tarski(A_34,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_46])).

tff(c_210,plain,(
    ! [D_62,B_63,C_64,A_65] :
      ( m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(B_63,C_64)))
      | ~ r1_tarski(k1_relat_1(D_62),B_63)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(A_65,C_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_218,plain,(
    ! [B_67] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_67,'#skF_3')))
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_67) ) ),
    inference(resolution,[status(thm)],[c_30,c_210])).

tff(c_18,plain,(
    ! [C_15,A_13,B_14] :
      ( v4_relat_1(C_15,A_13)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_240,plain,(
    ! [B_68] :
      ( v4_relat_1('#skF_5',B_68)
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_68) ) ),
    inference(resolution,[status(thm)],[c_218,c_18])).

tff(c_256,plain,
    ( v4_relat_1('#skF_5','#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_55,c_240])).

tff(c_260,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_263,plain,
    ( ~ v4_relat_1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_260])).

tff(c_267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_98,c_263])).

tff(c_269,plain,(
    r1_tarski(k1_relat_1('#skF_5'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_76,plain,(
    ! [C_39,B_40,A_41] :
      ( v5_relat_1(C_39,B_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_41,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_80,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_76])).

tff(c_81,plain,(
    ! [B_42,A_43] :
      ( r1_tarski(k2_relat_1(B_42),A_43)
      | ~ v5_relat_1(B_42,A_43)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_54,plain,(
    ! [A_34] :
      ( r1_tarski(A_34,'#skF_4')
      | ~ r1_tarski(A_34,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_46])).

tff(c_91,plain,(
    ! [B_42] :
      ( r1_tarski(k2_relat_1(B_42),'#skF_4')
      | ~ v5_relat_1(B_42,'#skF_3')
      | ~ v1_relat_1(B_42) ) ),
    inference(resolution,[status(thm)],[c_81,c_54])).

tff(c_142,plain,(
    ! [D_53,C_54,B_55,A_56] :
      ( m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(C_54,B_55)))
      | ~ r1_tarski(k2_relat_1(D_53),B_55)
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(C_54,A_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_145,plain,(
    ! [B_55] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_55)))
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_55) ) ),
    inference(resolution,[status(thm)],[c_30,c_142])).

tff(c_315,plain,(
    ! [B_73,B_74] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(B_73,B_74)))
      | ~ r1_tarski(k1_relat_1('#skF_5'),B_73)
      | ~ r1_tarski(k2_relat_1('#skF_5'),B_74) ) ),
    inference(resolution,[status(thm)],[c_145,c_210])).

tff(c_24,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_339,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_315,c_24])).

tff(c_340,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_339])).

tff(c_343,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_91,c_340])).

tff(c_350,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_80,c_343])).

tff(c_351,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_355,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_55,c_351])).

tff(c_362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_355])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.31  
% 2.33/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.32  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.33/1.32  
% 2.33/1.32  %Foreground sorts:
% 2.33/1.32  
% 2.33/1.32  
% 2.33/1.32  %Background operators:
% 2.33/1.32  
% 2.33/1.32  
% 2.33/1.32  %Foreground operators:
% 2.33/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.33/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.33/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.33/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.33/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.33/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.33/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.33/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.33/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.33/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.32  
% 2.33/1.34  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.33/1.34  tff(f_79, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_relset_1)).
% 2.33/1.34  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.33/1.34  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.33/1.34  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.33/1.34  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.33/1.34  tff(f_64, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 2.33/1.34  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.33/1.34  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 2.33/1.34  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.33/1.34  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.33/1.34  tff(c_32, plain, (![B_26, A_27]: (v1_relat_1(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_27)) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.33/1.34  tff(c_35, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_32])).
% 2.33/1.34  tff(c_38, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_35])).
% 2.33/1.34  tff(c_94, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.33/1.34  tff(c_98, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_94])).
% 2.33/1.34  tff(c_8, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(B_8), A_7) | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.33/1.34  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.33/1.34  tff(c_46, plain, (![A_34, C_35, B_36]: (r1_tarski(A_34, C_35) | ~r1_tarski(B_36, C_35) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.34  tff(c_55, plain, (![A_34]: (r1_tarski(A_34, '#skF_2') | ~r1_tarski(A_34, '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_46])).
% 2.33/1.34  tff(c_210, plain, (![D_62, B_63, C_64, A_65]: (m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(B_63, C_64))) | ~r1_tarski(k1_relat_1(D_62), B_63) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(A_65, C_64))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.33/1.34  tff(c_218, plain, (![B_67]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_67, '#skF_3'))) | ~r1_tarski(k1_relat_1('#skF_5'), B_67))), inference(resolution, [status(thm)], [c_30, c_210])).
% 2.33/1.34  tff(c_18, plain, (![C_15, A_13, B_14]: (v4_relat_1(C_15, A_13) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.33/1.34  tff(c_240, plain, (![B_68]: (v4_relat_1('#skF_5', B_68) | ~r1_tarski(k1_relat_1('#skF_5'), B_68))), inference(resolution, [status(thm)], [c_218, c_18])).
% 2.33/1.34  tff(c_256, plain, (v4_relat_1('#skF_5', '#skF_2') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_55, c_240])).
% 2.33/1.34  tff(c_260, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_1')), inference(splitLeft, [status(thm)], [c_256])).
% 2.33/1.34  tff(c_263, plain, (~v4_relat_1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_8, c_260])).
% 2.33/1.34  tff(c_267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_98, c_263])).
% 2.33/1.34  tff(c_269, plain, (r1_tarski(k1_relat_1('#skF_5'), '#skF_1')), inference(splitRight, [status(thm)], [c_256])).
% 2.33/1.34  tff(c_76, plain, (![C_39, B_40, A_41]: (v5_relat_1(C_39, B_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_41, B_40))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.33/1.34  tff(c_80, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_76])).
% 2.33/1.34  tff(c_81, plain, (![B_42, A_43]: (r1_tarski(k2_relat_1(B_42), A_43) | ~v5_relat_1(B_42, A_43) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.33/1.34  tff(c_26, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.33/1.34  tff(c_54, plain, (![A_34]: (r1_tarski(A_34, '#skF_4') | ~r1_tarski(A_34, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_46])).
% 2.33/1.34  tff(c_91, plain, (![B_42]: (r1_tarski(k2_relat_1(B_42), '#skF_4') | ~v5_relat_1(B_42, '#skF_3') | ~v1_relat_1(B_42))), inference(resolution, [status(thm)], [c_81, c_54])).
% 2.33/1.34  tff(c_142, plain, (![D_53, C_54, B_55, A_56]: (m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1(C_54, B_55))) | ~r1_tarski(k2_relat_1(D_53), B_55) | ~m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1(C_54, A_56))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.33/1.34  tff(c_145, plain, (![B_55]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_55))) | ~r1_tarski(k2_relat_1('#skF_5'), B_55))), inference(resolution, [status(thm)], [c_30, c_142])).
% 2.33/1.34  tff(c_315, plain, (![B_73, B_74]: (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(B_73, B_74))) | ~r1_tarski(k1_relat_1('#skF_5'), B_73) | ~r1_tarski(k2_relat_1('#skF_5'), B_74))), inference(resolution, [status(thm)], [c_145, c_210])).
% 2.33/1.34  tff(c_24, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.33/1.34  tff(c_339, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_315, c_24])).
% 2.33/1.34  tff(c_340, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_339])).
% 2.33/1.34  tff(c_343, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_91, c_340])).
% 2.33/1.34  tff(c_350, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_80, c_343])).
% 2.33/1.34  tff(c_351, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(splitRight, [status(thm)], [c_339])).
% 2.33/1.34  tff(c_355, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_55, c_351])).
% 2.33/1.34  tff(c_362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_269, c_355])).
% 2.33/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.34  
% 2.33/1.34  Inference rules
% 2.33/1.34  ----------------------
% 2.33/1.34  #Ref     : 0
% 2.33/1.34  #Sup     : 67
% 2.33/1.34  #Fact    : 0
% 2.33/1.34  #Define  : 0
% 2.33/1.34  #Split   : 6
% 2.33/1.34  #Chain   : 0
% 2.33/1.34  #Close   : 0
% 2.33/1.34  
% 2.33/1.34  Ordering : KBO
% 2.33/1.34  
% 2.33/1.34  Simplification rules
% 2.33/1.34  ----------------------
% 2.33/1.34  #Subsume      : 8
% 2.33/1.34  #Demod        : 28
% 2.33/1.34  #Tautology    : 14
% 2.33/1.34  #SimpNegUnit  : 0
% 2.33/1.34  #BackRed      : 0
% 2.33/1.34  
% 2.33/1.34  #Partial instantiations: 0
% 2.33/1.34  #Strategies tried      : 1
% 2.33/1.34  
% 2.33/1.34  Timing (in seconds)
% 2.33/1.34  ----------------------
% 2.33/1.34  Preprocessing        : 0.27
% 2.33/1.34  Parsing              : 0.15
% 2.33/1.34  CNF conversion       : 0.02
% 2.33/1.34  Main loop            : 0.29
% 2.33/1.34  Inferencing          : 0.12
% 2.33/1.34  Reduction            : 0.08
% 2.33/1.34  Demodulation         : 0.05
% 2.33/1.34  BG Simplification    : 0.01
% 2.33/1.34  Subsumption          : 0.06
% 2.33/1.34  Abstraction          : 0.01
% 2.33/1.34  MUC search           : 0.00
% 2.33/1.34  Cooper               : 0.00
% 2.33/1.34  Total                : 0.61
% 2.33/1.34  Index Insertion      : 0.00
% 2.33/1.34  Index Deletion       : 0.00
% 2.33/1.34  Index Matching       : 0.00
% 2.33/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
