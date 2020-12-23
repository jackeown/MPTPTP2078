%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:18 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 110 expanded)
%              Number of leaves         :   33 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  111 ( 263 expanded)
%              Number of equality atoms :   25 (  42 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v5_relat_1(C,A)
                  & v1_funct_1(C) )
               => k1_relat_1(k5_relat_1(C,B)) = k1_relat_1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t200_funct_2)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_10,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_56,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_59,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_38,c_56])).

tff(c_62,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_59])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_63,plain,(
    ! [C_36,A_37,B_38] :
      ( v4_relat_1(C_36,A_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_67,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_63])).

tff(c_84,plain,(
    ! [B_47,A_48] :
      ( k1_relat_1(B_47) = A_48
      | ~ v1_partfun1(B_47,A_48)
      | ~ v4_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_87,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_67,c_84])).

tff(c_90,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_87])).

tff(c_91,plain,(
    ~ v1_partfun1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_42,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_40,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_205,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_partfun1(C_57,A_58)
      | ~ v1_funct_2(C_57,A_58,B_59)
      | ~ v1_funct_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | v1_xboole_0(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_208,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_205])).

tff(c_211,plain,
    ( v1_partfun1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_208])).

tff(c_213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_91,c_211])).

tff(c_214,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_247,plain,(
    ! [A_64,B_65] :
      ( k10_relat_1(A_64,k1_relat_1(B_65)) = k1_relat_1(k5_relat_1(A_64,B_65))
      | ~ v1_relat_1(B_65)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_256,plain,(
    ! [A_64] :
      ( k1_relat_1(k5_relat_1(A_64,'#skF_2')) = k10_relat_1(A_64,'#skF_1')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_247])).

tff(c_261,plain,(
    ! [A_66] :
      ( k1_relat_1(k5_relat_1(A_66,'#skF_2')) = k10_relat_1(A_66,'#skF_1')
      | ~ v1_relat_1(A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_256])).

tff(c_30,plain,(
    k1_relat_1(k5_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_273,plain,
    ( k10_relat_1('#skF_3','#skF_1') != k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_30])).

tff(c_279,plain,(
    k10_relat_1('#skF_3','#skF_1') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_273])).

tff(c_34,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_74,plain,(
    ! [B_44,A_45] :
      ( r1_tarski(k2_relat_1(B_44),A_45)
      | ~ v5_relat_1(B_44,A_45)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_235,plain,(
    ! [B_62,A_63] :
      ( k3_xboole_0(k2_relat_1(B_62),A_63) = k2_relat_1(B_62)
      | ~ v5_relat_1(B_62,A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_74,c_2])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k10_relat_1(B_11,k3_xboole_0(k2_relat_1(B_11),A_10)) = k10_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_281,plain,(
    ! [B_67,A_68] :
      ( k10_relat_1(B_67,k2_relat_1(B_67)) = k10_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67)
      | ~ v5_relat_1(B_67,A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_12])).

tff(c_285,plain,
    ( k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_281])).

tff(c_291,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_285])).

tff(c_14,plain,(
    ! [A_12] :
      ( k10_relat_1(A_12,k2_relat_1(A_12)) = k1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_323,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_14])).

tff(c_330,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_323])).

tff(c_332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_330])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:28:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.25  
% 2.22/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.25  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.22/1.25  
% 2.22/1.25  %Foreground sorts:
% 2.22/1.25  
% 2.22/1.25  
% 2.22/1.25  %Background operators:
% 2.22/1.25  
% 2.22/1.25  
% 2.22/1.25  %Foreground operators:
% 2.22/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.22/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.25  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.22/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.22/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.22/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.25  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.22/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.25  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.22/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.25  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.22/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.22/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.25  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.22/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.22/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.25  
% 2.22/1.26  tff(f_107, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (k1_relat_1(k5_relat_1(C, B)) = k1_relat_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t200_funct_2)).
% 2.22/1.26  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.22/1.26  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.22/1.26  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.22/1.26  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 2.22/1.26  tff(f_79, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.22/1.26  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t182_relat_1)).
% 2.22/1.26  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.22/1.26  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.22/1.26  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 2.22/1.26  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.22/1.26  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.22/1.26  tff(c_10, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.22/1.26  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.22/1.26  tff(c_56, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.22/1.26  tff(c_59, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_38, c_56])).
% 2.22/1.26  tff(c_62, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_59])).
% 2.22/1.26  tff(c_44, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.22/1.26  tff(c_63, plain, (![C_36, A_37, B_38]: (v4_relat_1(C_36, A_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.22/1.26  tff(c_67, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_63])).
% 2.22/1.26  tff(c_84, plain, (![B_47, A_48]: (k1_relat_1(B_47)=A_48 | ~v1_partfun1(B_47, A_48) | ~v4_relat_1(B_47, A_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.22/1.26  tff(c_87, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_67, c_84])).
% 2.22/1.26  tff(c_90, plain, (k1_relat_1('#skF_2')='#skF_1' | ~v1_partfun1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_87])).
% 2.22/1.26  tff(c_91, plain, (~v1_partfun1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_90])).
% 2.22/1.26  tff(c_42, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.22/1.26  tff(c_40, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.22/1.26  tff(c_205, plain, (![C_57, A_58, B_59]: (v1_partfun1(C_57, A_58) | ~v1_funct_2(C_57, A_58, B_59) | ~v1_funct_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | v1_xboole_0(B_59))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.22/1.26  tff(c_208, plain, (v1_partfun1('#skF_2', '#skF_1') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_205])).
% 2.22/1.26  tff(c_211, plain, (v1_partfun1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_208])).
% 2.22/1.26  tff(c_213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_91, c_211])).
% 2.22/1.26  tff(c_214, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_90])).
% 2.22/1.26  tff(c_247, plain, (![A_64, B_65]: (k10_relat_1(A_64, k1_relat_1(B_65))=k1_relat_1(k5_relat_1(A_64, B_65)) | ~v1_relat_1(B_65) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.22/1.26  tff(c_256, plain, (![A_64]: (k1_relat_1(k5_relat_1(A_64, '#skF_2'))=k10_relat_1(A_64, '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(A_64))), inference(superposition, [status(thm), theory('equality')], [c_214, c_247])).
% 2.22/1.26  tff(c_261, plain, (![A_66]: (k1_relat_1(k5_relat_1(A_66, '#skF_2'))=k10_relat_1(A_66, '#skF_1') | ~v1_relat_1(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_256])).
% 2.22/1.26  tff(c_30, plain, (k1_relat_1(k5_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.22/1.26  tff(c_273, plain, (k10_relat_1('#skF_3', '#skF_1')!=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_261, c_30])).
% 2.22/1.26  tff(c_279, plain, (k10_relat_1('#skF_3', '#skF_1')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_273])).
% 2.22/1.26  tff(c_34, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.22/1.26  tff(c_74, plain, (![B_44, A_45]: (r1_tarski(k2_relat_1(B_44), A_45) | ~v5_relat_1(B_44, A_45) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.22/1.26  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.22/1.26  tff(c_235, plain, (![B_62, A_63]: (k3_xboole_0(k2_relat_1(B_62), A_63)=k2_relat_1(B_62) | ~v5_relat_1(B_62, A_63) | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_74, c_2])).
% 2.22/1.26  tff(c_12, plain, (![B_11, A_10]: (k10_relat_1(B_11, k3_xboole_0(k2_relat_1(B_11), A_10))=k10_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.22/1.26  tff(c_281, plain, (![B_67, A_68]: (k10_relat_1(B_67, k2_relat_1(B_67))=k10_relat_1(B_67, A_68) | ~v1_relat_1(B_67) | ~v5_relat_1(B_67, A_68) | ~v1_relat_1(B_67))), inference(superposition, [status(thm), theory('equality')], [c_235, c_12])).
% 2.22/1.26  tff(c_285, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_281])).
% 2.22/1.26  tff(c_291, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_285])).
% 2.22/1.26  tff(c_14, plain, (![A_12]: (k10_relat_1(A_12, k2_relat_1(A_12))=k1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.22/1.26  tff(c_323, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_291, c_14])).
% 2.22/1.26  tff(c_330, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_323])).
% 2.22/1.26  tff(c_332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_279, c_330])).
% 2.22/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.26  
% 2.22/1.26  Inference rules
% 2.22/1.26  ----------------------
% 2.22/1.26  #Ref     : 0
% 2.22/1.26  #Sup     : 67
% 2.22/1.26  #Fact    : 0
% 2.22/1.26  #Define  : 0
% 2.22/1.26  #Split   : 1
% 2.22/1.26  #Chain   : 0
% 2.22/1.26  #Close   : 0
% 2.22/1.26  
% 2.22/1.26  Ordering : KBO
% 2.22/1.26  
% 2.22/1.26  Simplification rules
% 2.22/1.26  ----------------------
% 2.22/1.26  #Subsume      : 0
% 2.22/1.26  #Demod        : 36
% 2.22/1.26  #Tautology    : 46
% 2.22/1.26  #SimpNegUnit  : 3
% 2.22/1.26  #BackRed      : 3
% 2.22/1.26  
% 2.22/1.26  #Partial instantiations: 0
% 2.22/1.26  #Strategies tried      : 1
% 2.22/1.26  
% 2.22/1.26  Timing (in seconds)
% 2.22/1.26  ----------------------
% 2.22/1.26  Preprocessing        : 0.31
% 2.22/1.27  Parsing              : 0.16
% 2.22/1.27  CNF conversion       : 0.02
% 2.22/1.27  Main loop            : 0.20
% 2.22/1.27  Inferencing          : 0.08
% 2.22/1.27  Reduction            : 0.06
% 2.22/1.27  Demodulation         : 0.04
% 2.22/1.27  BG Simplification    : 0.01
% 2.22/1.27  Subsumption          : 0.02
% 2.38/1.27  Abstraction          : 0.01
% 2.38/1.27  MUC search           : 0.00
% 2.38/1.27  Cooper               : 0.00
% 2.38/1.27  Total                : 0.54
% 2.38/1.27  Index Insertion      : 0.00
% 2.38/1.27  Index Deletion       : 0.00
% 2.38/1.27  Index Matching       : 0.00
% 2.38/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
