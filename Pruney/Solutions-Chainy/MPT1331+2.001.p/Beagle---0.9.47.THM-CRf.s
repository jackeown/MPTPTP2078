%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:13 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 439 expanded)
%              Number of leaves         :   38 ( 169 expanded)
%              Depth                    :   15
%              Number of atoms          :  132 (1147 expanded)
%              Number of equality atoms :   10 ( 164 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k9_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_funct_3 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_funct_3,type,(
    k3_funct_3: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
                   => m1_subset_1(k9_relat_1(k3_funct_3(C),D),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_2)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => r1_tarski(k2_relat_1(k3_funct_3(A)),k1_zfmisc_1(k1_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_funct_3)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k3_funct_3(A))
        & v1_funct_1(k3_funct_3(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_3)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( r1_tarski(C,B)
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).

tff(c_48,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_49,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_57,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_49])).

tff(c_44,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_56,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_49])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_56,c_38])).

tff(c_92,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_92])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_30,plain,(
    ! [A_20] :
      ( r1_tarski(k2_relat_1(k3_funct_3(A_20)),k1_zfmisc_1(k1_relat_1(A_20)))
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    ! [A_19] :
      ( v1_relat_1(k3_funct_3(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_109,plain,(
    ! [C_55,A_56,B_57] :
      ( v4_relat_1(C_55,A_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_118,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_109])).

tff(c_143,plain,(
    ! [B_69,A_70] :
      ( k1_relat_1(B_69) = A_70
      | ~ v1_partfun1(B_69,A_70)
      | ~ v4_relat_1(B_69,A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_146,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_143])).

tff(c_149,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_146])).

tff(c_150,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_40,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_59,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_40])).

tff(c_69,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_59])).

tff(c_215,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_partfun1(C_77,A_78)
      | ~ v1_funct_2(C_77,A_78,B_79)
      | ~ v1_funct_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | v1_xboole_0(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_222,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_215])).

tff(c_226,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_69,c_222])).

tff(c_227,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_226])).

tff(c_24,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(k2_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_230,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_227,c_24])).

tff(c_233,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_230])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_233])).

tff(c_236,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_244,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_57])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k9_relat_1(B_4,A_3),k2_relat_1(B_4))
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_288,plain,(
    ! [C_80,A_81,B_82] :
      ( m1_subset_1(C_80,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_81))))
      | ~ r1_tarski(C_80,B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_81))))
      | ~ l1_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_411,plain,(
    ! [B_93,A_94,A_95] :
      ( m1_subset_1(k9_relat_1(B_93,A_94),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_95))))
      | ~ m1_subset_1(k2_relat_1(B_93),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_95))))
      | ~ l1_struct_0(A_95)
      | ~ v1_relat_1(B_93) ) ),
    inference(resolution,[status(thm)],[c_6,c_288])).

tff(c_417,plain,(
    ! [B_93,A_94] :
      ( m1_subset_1(k9_relat_1(B_93,A_94),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_3'))))
      | ~ m1_subset_1(k2_relat_1(B_93),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_struct_0('#skF_1')
      | ~ v1_relat_1(B_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_411])).

tff(c_463,plain,(
    ! [B_105,A_106] :
      ( m1_subset_1(k9_relat_1(B_105,A_106),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_3'))))
      | ~ m1_subset_1(k2_relat_1(B_105),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_3'))))
      | ~ v1_relat_1(B_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_244,c_417])).

tff(c_34,plain,(
    ~ m1_subset_1(k9_relat_1(k3_funct_3('#skF_3'),'#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_87,plain,(
    ~ m1_subset_1(k9_relat_1(k3_funct_3('#skF_3'),'#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_34])).

tff(c_240,plain,(
    ~ m1_subset_1(k9_relat_1(k3_funct_3('#skF_3'),'#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_87])).

tff(c_470,plain,
    ( ~ m1_subset_1(k2_relat_1(k3_funct_3('#skF_3')),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_3'))))
    | ~ v1_relat_1(k3_funct_3('#skF_3')) ),
    inference(resolution,[status(thm)],[c_463,c_240])).

tff(c_472,plain,(
    ~ v1_relat_1(k3_funct_3('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_470])).

tff(c_475,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_472])).

tff(c_479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_42,c_475])).

tff(c_480,plain,(
    ~ m1_subset_1(k2_relat_1(k3_funct_3('#skF_3')),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_470])).

tff(c_485,plain,(
    ~ r1_tarski(k2_relat_1(k3_funct_3('#skF_3')),k1_zfmisc_1(k1_relat_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_4,c_480])).

tff(c_504,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_485])).

tff(c_508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_42,c_504])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.43  
% 2.81/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.43  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k9_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_funct_3 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.81/1.43  
% 2.81/1.43  %Foreground sorts:
% 2.81/1.43  
% 2.81/1.43  
% 2.81/1.43  %Background operators:
% 2.81/1.43  
% 2.81/1.43  
% 2.81/1.43  %Foreground operators:
% 2.81/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.81/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.81/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.43  tff(k3_funct_3, type, k3_funct_3: $i > $i).
% 2.81/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.81/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.81/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.43  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.81/1.43  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.81/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.81/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.81/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.81/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.81/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.81/1.43  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.81/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.81/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.81/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.43  
% 2.90/1.45  tff(f_122, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(k9_relat_1(k3_funct_3(C), D), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_2)).
% 2.90/1.45  tff(f_69, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.90/1.45  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.90/1.45  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => r1_tarski(k2_relat_1(k3_funct_3(A)), k1_zfmisc_1(k1_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_funct_3)).
% 2.90/1.45  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.90/1.45  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k3_funct_3(A)) & v1_funct_1(k3_funct_3(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_funct_3)).
% 2.90/1.45  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.90/1.45  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 2.90/1.45  tff(f_57, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 2.90/1.45  tff(f_77, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.90/1.45  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 2.90/1.45  tff(f_101, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (r1_tarski(C, B) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_tops_2)).
% 2.90/1.45  tff(c_48, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.90/1.45  tff(c_49, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.90/1.45  tff(c_57, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_48, c_49])).
% 2.90/1.45  tff(c_44, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.90/1.45  tff(c_56, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_49])).
% 2.90/1.45  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.90/1.45  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_56, c_38])).
% 2.90/1.45  tff(c_92, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.90/1.45  tff(c_101, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_92])).
% 2.90/1.45  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.90/1.45  tff(c_30, plain, (![A_20]: (r1_tarski(k2_relat_1(k3_funct_3(A_20)), k1_zfmisc_1(k1_relat_1(A_20))) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.90/1.45  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.90/1.45  tff(c_28, plain, (![A_19]: (v1_relat_1(k3_funct_3(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.90/1.45  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.90/1.45  tff(c_109, plain, (![C_55, A_56, B_57]: (v4_relat_1(C_55, A_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.90/1.45  tff(c_118, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_109])).
% 2.90/1.45  tff(c_143, plain, (![B_69, A_70]: (k1_relat_1(B_69)=A_70 | ~v1_partfun1(B_69, A_70) | ~v4_relat_1(B_69, A_70) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.90/1.45  tff(c_146, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_118, c_143])).
% 2.90/1.45  tff(c_149, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_146])).
% 2.90/1.45  tff(c_150, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_149])).
% 2.90/1.45  tff(c_40, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.90/1.45  tff(c_59, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_40])).
% 2.90/1.45  tff(c_69, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_59])).
% 2.90/1.45  tff(c_215, plain, (![C_77, A_78, B_79]: (v1_partfun1(C_77, A_78) | ~v1_funct_2(C_77, A_78, B_79) | ~v1_funct_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | v1_xboole_0(B_79))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.90/1.45  tff(c_222, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_68, c_215])).
% 2.90/1.45  tff(c_226, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_69, c_222])).
% 2.90/1.45  tff(c_227, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_150, c_226])).
% 2.90/1.45  tff(c_24, plain, (![A_18]: (~v1_xboole_0(k2_struct_0(A_18)) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.90/1.45  tff(c_230, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_227, c_24])).
% 2.90/1.45  tff(c_233, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_230])).
% 2.90/1.45  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_233])).
% 2.90/1.45  tff(c_236, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_149])).
% 2.90/1.45  tff(c_244, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_236, c_57])).
% 2.90/1.45  tff(c_6, plain, (![B_4, A_3]: (r1_tarski(k9_relat_1(B_4, A_3), k2_relat_1(B_4)) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.90/1.45  tff(c_288, plain, (![C_80, A_81, B_82]: (m1_subset_1(C_80, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_81)))) | ~r1_tarski(C_80, B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_81)))) | ~l1_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.90/1.45  tff(c_411, plain, (![B_93, A_94, A_95]: (m1_subset_1(k9_relat_1(B_93, A_94), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_95)))) | ~m1_subset_1(k2_relat_1(B_93), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_95)))) | ~l1_struct_0(A_95) | ~v1_relat_1(B_93))), inference(resolution, [status(thm)], [c_6, c_288])).
% 2.90/1.45  tff(c_417, plain, (![B_93, A_94]: (m1_subset_1(k9_relat_1(B_93, A_94), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_3')))) | ~m1_subset_1(k2_relat_1(B_93), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_struct_0('#skF_1') | ~v1_relat_1(B_93))), inference(superposition, [status(thm), theory('equality')], [c_244, c_411])).
% 2.90/1.45  tff(c_463, plain, (![B_105, A_106]: (m1_subset_1(k9_relat_1(B_105, A_106), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_3')))) | ~m1_subset_1(k2_relat_1(B_105), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_3')))) | ~v1_relat_1(B_105))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_244, c_417])).
% 2.90/1.45  tff(c_34, plain, (~m1_subset_1(k9_relat_1(k3_funct_3('#skF_3'), '#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.90/1.45  tff(c_87, plain, (~m1_subset_1(k9_relat_1(k3_funct_3('#skF_3'), '#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_34])).
% 2.90/1.45  tff(c_240, plain, (~m1_subset_1(k9_relat_1(k3_funct_3('#skF_3'), '#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_87])).
% 2.90/1.45  tff(c_470, plain, (~m1_subset_1(k2_relat_1(k3_funct_3('#skF_3')), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_3')))) | ~v1_relat_1(k3_funct_3('#skF_3'))), inference(resolution, [status(thm)], [c_463, c_240])).
% 2.90/1.45  tff(c_472, plain, (~v1_relat_1(k3_funct_3('#skF_3'))), inference(splitLeft, [status(thm)], [c_470])).
% 2.90/1.45  tff(c_475, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_472])).
% 2.90/1.45  tff(c_479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_42, c_475])).
% 2.90/1.45  tff(c_480, plain, (~m1_subset_1(k2_relat_1(k3_funct_3('#skF_3')), k1_zfmisc_1(k1_zfmisc_1(k1_relat_1('#skF_3'))))), inference(splitRight, [status(thm)], [c_470])).
% 2.90/1.45  tff(c_485, plain, (~r1_tarski(k2_relat_1(k3_funct_3('#skF_3')), k1_zfmisc_1(k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_4, c_480])).
% 2.90/1.45  tff(c_504, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_485])).
% 2.90/1.45  tff(c_508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_42, c_504])).
% 2.90/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.45  
% 2.90/1.45  Inference rules
% 2.90/1.45  ----------------------
% 2.90/1.45  #Ref     : 0
% 2.90/1.45  #Sup     : 92
% 2.90/1.45  #Fact    : 0
% 2.90/1.45  #Define  : 0
% 2.90/1.45  #Split   : 8
% 2.90/1.45  #Chain   : 0
% 2.90/1.45  #Close   : 0
% 2.90/1.45  
% 2.90/1.45  Ordering : KBO
% 2.90/1.45  
% 2.90/1.45  Simplification rules
% 2.90/1.45  ----------------------
% 2.90/1.45  #Subsume      : 6
% 2.90/1.45  #Demod        : 87
% 2.90/1.45  #Tautology    : 28
% 2.90/1.45  #SimpNegUnit  : 2
% 2.90/1.45  #BackRed      : 9
% 2.90/1.45  
% 2.90/1.45  #Partial instantiations: 0
% 2.90/1.45  #Strategies tried      : 1
% 2.90/1.45  
% 2.90/1.45  Timing (in seconds)
% 2.90/1.45  ----------------------
% 2.90/1.45  Preprocessing        : 0.34
% 2.90/1.45  Parsing              : 0.18
% 2.90/1.45  CNF conversion       : 0.02
% 2.90/1.45  Main loop            : 0.30
% 2.90/1.45  Inferencing          : 0.11
% 2.90/1.45  Reduction            : 0.10
% 2.90/1.45  Demodulation         : 0.07
% 2.90/1.45  BG Simplification    : 0.02
% 2.90/1.45  Subsumption          : 0.05
% 2.90/1.45  Abstraction          : 0.02
% 2.90/1.45  MUC search           : 0.00
% 2.90/1.45  Cooper               : 0.00
% 2.90/1.45  Total                : 0.67
% 2.90/1.45  Index Insertion      : 0.00
% 2.90/1.45  Index Deletion       : 0.00
% 2.90/1.45  Index Matching       : 0.00
% 2.90/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
