%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:18 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 111 expanded)
%              Number of leaves         :   35 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  120 ( 268 expanded)
%              Number of equality atoms :   25 (  41 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_funct_2)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_14,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    ! [A_17] : v1_funct_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ! [A_18] :
      ( k1_relat_1(k6_relat_1(A_18)) = A_18
      | ~ v1_funct_1(k6_relat_1(A_18))
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_54,plain,(
    ! [A_18] :
      ( k1_relat_1(k6_relat_1(A_18)) = A_18
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_24])).

tff(c_58,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_54])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_166,plain,(
    ! [B_67,A_68] :
      ( k5_relat_1(B_67,k6_relat_1(A_68)) = B_67
      | ~ r1_tarski(k2_relat_1(B_67),A_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_170,plain,(
    ! [B_5,A_4] :
      ( k5_relat_1(B_5,k6_relat_1(A_4)) = B_5
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_166])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_82,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_82])).

tff(c_88,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_85])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_89,plain,(
    ! [C_45,A_46,B_47] :
      ( v4_relat_1(C_45,A_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_93,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_89])).

tff(c_112,plain,(
    ! [B_57,A_58] :
      ( k1_relat_1(B_57) = A_58
      | ~ v1_partfun1(B_57,A_58)
      | ~ v4_relat_1(B_57,A_58)
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_115,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_112])).

tff(c_118,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_115])).

tff(c_119,plain,(
    ~ v1_partfun1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_48,plain,(
    v1_funct_2('#skF_3','#skF_2','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_145,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_partfun1(C_64,A_65)
      | ~ v1_funct_2(C_64,A_65,B_66)
      | ~ v1_funct_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | v1_xboole_0(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_148,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | ~ v1_funct_2('#skF_3','#skF_2','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_145])).

tff(c_151,plain,
    ( v1_partfun1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_148])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_119,c_151])).

tff(c_154,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_261,plain,(
    ! [C_77,B_78,A_79] :
      ( k1_relat_1(k5_relat_1(C_77,B_78)) = k1_relat_1(k5_relat_1(C_77,A_79))
      | k1_relat_1(B_78) != k1_relat_1(A_79)
      | ~ v1_relat_1(C_77)
      | ~ v1_relat_1(B_78)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_38,plain,(
    k1_relat_1(k5_relat_1('#skF_4','#skF_3')) != k1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_294,plain,(
    ! [B_78] :
      ( k1_relat_1(k5_relat_1('#skF_4',B_78)) != k1_relat_1('#skF_4')
      | k1_relat_1(B_78) != k1_relat_1('#skF_3')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(B_78)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_38])).

tff(c_324,plain,(
    ! [B_80] :
      ( k1_relat_1(k5_relat_1('#skF_4',B_80)) != k1_relat_1('#skF_4')
      | k1_relat_1(B_80) != '#skF_2'
      | ~ v1_relat_1(B_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_44,c_154,c_294])).

tff(c_336,plain,(
    ! [A_4] :
      ( k1_relat_1(k6_relat_1(A_4)) != '#skF_2'
      | ~ v1_relat_1(k6_relat_1(A_4))
      | ~ v5_relat_1('#skF_4',A_4)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_324])).

tff(c_344,plain,(
    ~ v5_relat_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_14,c_58,c_336])).

tff(c_42,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_344,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:31:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.28  
% 2.33/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.29  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.33/1.29  
% 2.33/1.29  %Foreground sorts:
% 2.33/1.29  
% 2.33/1.29  
% 2.33/1.29  %Background operators:
% 2.33/1.29  
% 2.33/1.29  
% 2.33/1.29  %Foreground operators:
% 2.33/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.33/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.29  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.33/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.33/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.33/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.29  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.33/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.33/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.33/1.29  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.33/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.33/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.33/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.33/1.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.33/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.33/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.33/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.33/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.33/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.29  
% 2.33/1.30  tff(f_123, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) => (k1_relat_1(k5_relat_1(C, B)) = k1_relat_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t200_funct_2)).
% 2.33/1.30  tff(f_62, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.33/1.30  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 2.33/1.30  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.33/1.30  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.33/1.30  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.33/1.30  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.33/1.30  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.33/1.30  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.33/1.30  tff(f_95, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.33/1.30  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t198_relat_1)).
% 2.33/1.30  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.33/1.30  tff(c_14, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.33/1.30  tff(c_16, plain, (![A_17]: (v1_funct_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.33/1.30  tff(c_24, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18 | ~v1_funct_1(k6_relat_1(A_18)) | ~v1_relat_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.33/1.30  tff(c_54, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18 | ~v1_relat_1(k6_relat_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_24])).
% 2.33/1.30  tff(c_58, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_54])).
% 2.33/1.30  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.33/1.30  tff(c_166, plain, (![B_67, A_68]: (k5_relat_1(B_67, k6_relat_1(A_68))=B_67 | ~r1_tarski(k2_relat_1(B_67), A_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.33/1.30  tff(c_170, plain, (![B_5, A_4]: (k5_relat_1(B_5, k6_relat_1(A_4))=B_5 | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_166])).
% 2.33/1.30  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.33/1.30  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.33/1.30  tff(c_82, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.33/1.30  tff(c_85, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_82])).
% 2.33/1.30  tff(c_88, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_85])).
% 2.33/1.30  tff(c_52, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.33/1.30  tff(c_89, plain, (![C_45, A_46, B_47]: (v4_relat_1(C_45, A_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.33/1.30  tff(c_93, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_89])).
% 2.33/1.30  tff(c_112, plain, (![B_57, A_58]: (k1_relat_1(B_57)=A_58 | ~v1_partfun1(B_57, A_58) | ~v4_relat_1(B_57, A_58) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.33/1.30  tff(c_115, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_93, c_112])).
% 2.33/1.30  tff(c_118, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v1_partfun1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_115])).
% 2.33/1.30  tff(c_119, plain, (~v1_partfun1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_118])).
% 2.33/1.30  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.33/1.30  tff(c_48, plain, (v1_funct_2('#skF_3', '#skF_2', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.33/1.30  tff(c_145, plain, (![C_64, A_65, B_66]: (v1_partfun1(C_64, A_65) | ~v1_funct_2(C_64, A_65, B_66) | ~v1_funct_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | v1_xboole_0(B_66))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.33/1.30  tff(c_148, plain, (v1_partfun1('#skF_3', '#skF_2') | ~v1_funct_2('#skF_3', '#skF_2', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_46, c_145])).
% 2.33/1.30  tff(c_151, plain, (v1_partfun1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_148])).
% 2.33/1.30  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_119, c_151])).
% 2.33/1.30  tff(c_154, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_118])).
% 2.33/1.30  tff(c_261, plain, (![C_77, B_78, A_79]: (k1_relat_1(k5_relat_1(C_77, B_78))=k1_relat_1(k5_relat_1(C_77, A_79)) | k1_relat_1(B_78)!=k1_relat_1(A_79) | ~v1_relat_1(C_77) | ~v1_relat_1(B_78) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.33/1.30  tff(c_38, plain, (k1_relat_1(k5_relat_1('#skF_4', '#skF_3'))!=k1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.33/1.30  tff(c_294, plain, (![B_78]: (k1_relat_1(k5_relat_1('#skF_4', B_78))!=k1_relat_1('#skF_4') | k1_relat_1(B_78)!=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1(B_78) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_261, c_38])).
% 2.33/1.30  tff(c_324, plain, (![B_80]: (k1_relat_1(k5_relat_1('#skF_4', B_80))!=k1_relat_1('#skF_4') | k1_relat_1(B_80)!='#skF_2' | ~v1_relat_1(B_80))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_44, c_154, c_294])).
% 2.33/1.30  tff(c_336, plain, (![A_4]: (k1_relat_1(k6_relat_1(A_4))!='#skF_2' | ~v1_relat_1(k6_relat_1(A_4)) | ~v5_relat_1('#skF_4', A_4) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_170, c_324])).
% 2.33/1.30  tff(c_344, plain, (~v5_relat_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_14, c_58, c_336])).
% 2.33/1.30  tff(c_42, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.33/1.30  tff(c_346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_344, c_42])).
% 2.33/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.30  
% 2.33/1.30  Inference rules
% 2.33/1.30  ----------------------
% 2.33/1.30  #Ref     : 0
% 2.33/1.30  #Sup     : 60
% 2.33/1.30  #Fact    : 0
% 2.33/1.30  #Define  : 0
% 2.33/1.30  #Split   : 2
% 2.33/1.30  #Chain   : 0
% 2.33/1.30  #Close   : 0
% 2.33/1.30  
% 2.33/1.30  Ordering : KBO
% 2.33/1.30  
% 2.33/1.30  Simplification rules
% 2.33/1.30  ----------------------
% 2.33/1.30  #Subsume      : 1
% 2.33/1.30  #Demod        : 67
% 2.33/1.30  #Tautology    : 28
% 2.33/1.30  #SimpNegUnit  : 4
% 2.33/1.30  #BackRed      : 2
% 2.33/1.30  
% 2.33/1.30  #Partial instantiations: 0
% 2.33/1.30  #Strategies tried      : 1
% 2.33/1.30  
% 2.33/1.30  Timing (in seconds)
% 2.33/1.30  ----------------------
% 2.33/1.30  Preprocessing        : 0.30
% 2.33/1.30  Parsing              : 0.16
% 2.33/1.30  CNF conversion       : 0.02
% 2.33/1.30  Main loop            : 0.24
% 2.33/1.30  Inferencing          : 0.09
% 2.33/1.30  Reduction            : 0.08
% 2.33/1.30  Demodulation         : 0.06
% 2.33/1.30  BG Simplification    : 0.02
% 2.33/1.30  Subsumption          : 0.04
% 2.33/1.30  Abstraction          : 0.01
% 2.33/1.30  MUC search           : 0.00
% 2.33/1.30  Cooper               : 0.00
% 2.33/1.30  Total                : 0.58
% 2.33/1.30  Index Insertion      : 0.00
% 2.33/1.30  Index Deletion       : 0.00
% 2.33/1.30  Index Matching       : 0.00
% 2.33/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
