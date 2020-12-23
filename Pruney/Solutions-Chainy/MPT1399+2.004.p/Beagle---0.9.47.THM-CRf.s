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
% DateTime   : Thu Dec  3 10:24:19 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 300 expanded)
%              Number of leaves         :   41 ( 121 expanded)
%              Depth                    :   12
%              Number of atoms          :  162 ( 872 expanded)
%              Number of equality atoms :    8 ( 109 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_142,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_114,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_29,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_31,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_68,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_88,plain,(
    ! [A_1] : r1_tarski('#skF_7',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_76,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_74,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_56,plain,(
    ! [A_29] :
      ( l1_struct_0(A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_105,plain,(
    ! [A_49] :
      ( u1_struct_0(A_49) = k2_struct_0(A_49)
      | ~ l1_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_111,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = k2_struct_0(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_56,c_105])).

tff(c_115,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_111])).

tff(c_194,plain,(
    ! [A_69] :
      ( m1_subset_1('#skF_4'(A_69),k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_200,plain,
    ( m1_subset_1('#skF_4'('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_194])).

tff(c_203,plain,
    ( m1_subset_1('#skF_4'('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_200])).

tff(c_204,plain,(
    m1_subset_1('#skF_4'('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_203])).

tff(c_8,plain,(
    ! [B_6,A_4] :
      ( v1_xboole_0(B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_4))
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_220,plain,
    ( v1_xboole_0('#skF_4'('#skF_5'))
    | ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_204,c_8])).

tff(c_234,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_72,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_117,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_72])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_58,plain,(
    ! [A_30] :
      ( v4_pre_topc(k2_struct_0(A_30),A_30)
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_152,plain,(
    ! [A_62] :
      ( r2_hidden(u1_struct_0(A_62),u1_pre_topc(A_62))
      | ~ v2_pre_topc(A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_158,plain,
    ( r2_hidden(k2_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_152])).

tff(c_161,plain,(
    r2_hidden(k2_struct_0('#skF_5'),u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_158])).

tff(c_4,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k2_subset_1(A_3),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [A_3] : m1_subset_1(A_3,k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_289,plain,(
    ! [B_75,A_76] :
      ( v3_pre_topc(B_75,A_76)
      | ~ r2_hidden(B_75,u1_pre_topc(A_76))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_304,plain,(
    ! [A_77] :
      ( v3_pre_topc(u1_struct_0(A_77),A_77)
      | ~ r2_hidden(u1_struct_0(A_77),u1_pre_topc(A_77))
      | ~ l1_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_87,c_289])).

tff(c_316,plain,
    ( v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5')
    | ~ r2_hidden(k2_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_304])).

tff(c_321,plain,(
    v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_161,c_115,c_316])).

tff(c_84,plain,(
    ! [D_44] :
      ( v4_pre_topc(D_44,'#skF_5')
      | ~ r2_hidden(D_44,'#skF_7')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_133,plain,(
    ! [D_55] :
      ( v4_pre_topc(D_55,'#skF_5')
      | ~ r2_hidden(D_55,'#skF_7')
      | ~ m1_subset_1(D_55,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_84])).

tff(c_138,plain,
    ( v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ r2_hidden(k2_struct_0('#skF_5'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_87,c_133])).

tff(c_166,plain,(
    ~ r2_hidden(k2_struct_0('#skF_5'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_80,plain,(
    ! [D_44] :
      ( r2_hidden(D_44,'#skF_7')
      | ~ r2_hidden('#skF_6',D_44)
      | ~ v4_pre_topc(D_44,'#skF_5')
      | ~ v3_pre_topc(D_44,'#skF_5')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_222,plain,(
    ! [D_70] :
      ( r2_hidden(D_70,'#skF_7')
      | ~ r2_hidden('#skF_6',D_70)
      | ~ v4_pre_topc(D_70,'#skF_5')
      | ~ v3_pre_topc(D_70,'#skF_5')
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_80])).

tff(c_229,plain,
    ( r2_hidden(k2_struct_0('#skF_5'),'#skF_7')
    | ~ r2_hidden('#skF_6',k2_struct_0('#skF_5'))
    | ~ v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_87,c_222])).

tff(c_233,plain,
    ( ~ r2_hidden('#skF_6',k2_struct_0('#skF_5'))
    | ~ v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_229])).

tff(c_386,plain,
    ( ~ r2_hidden('#skF_6',k2_struct_0('#skF_5'))
    | ~ v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_233])).

tff(c_387,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_386])).

tff(c_390,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_387])).

tff(c_394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_390])).

tff(c_395,plain,(
    ~ r2_hidden('#skF_6',k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_386])).

tff(c_399,plain,
    ( v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_10,c_395])).

tff(c_402,plain,(
    v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_399])).

tff(c_404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_402])).

tff(c_405,plain,(
    v1_xboole_0('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_64,plain,(
    ! [A_31] :
      ( ~ v1_xboole_0('#skF_4'(A_31))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_409,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_405,c_64])).

tff(c_412,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_409])).

tff(c_414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_412])).

tff(c_416,plain,(
    r2_hidden(k2_struct_0('#skF_5'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_419,plain,(
    ~ r1_tarski('#skF_7',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_416,c_12])).

tff(c_423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_419])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.40  
% 2.73/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.40  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3
% 2.73/1.40  
% 2.73/1.40  %Foreground sorts:
% 2.73/1.40  
% 2.73/1.40  
% 2.73/1.40  %Background operators:
% 2.73/1.40  
% 2.73/1.40  
% 2.73/1.40  %Foreground operators:
% 2.73/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.73/1.40  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.73/1.40  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.73/1.40  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.73/1.40  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.73/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.73/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.73/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.73/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.73/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.40  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.73/1.40  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.73/1.40  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.73/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.40  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.73/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.73/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.73/1.40  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.73/1.40  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.73/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.40  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.73/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.40  
% 2.73/1.43  tff(f_142, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.73/1.43  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.73/1.43  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.73/1.43  tff(f_78, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.73/1.43  tff(f_114, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_tops_1)).
% 2.73/1.43  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.73/1.43  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.73/1.43  tff(f_97, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.73/1.43  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 2.73/1.43  tff(f_29, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.73/1.43  tff(f_31, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.73/1.43  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.73/1.43  tff(f_49, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.73/1.43  tff(c_68, plain, (k1_xboole_0='#skF_7'), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.73/1.43  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.73/1.43  tff(c_88, plain, (![A_1]: (r1_tarski('#skF_7', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2])).
% 2.73/1.43  tff(c_78, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.73/1.43  tff(c_76, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.73/1.43  tff(c_74, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.73/1.43  tff(c_56, plain, (![A_29]: (l1_struct_0(A_29) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.73/1.43  tff(c_105, plain, (![A_49]: (u1_struct_0(A_49)=k2_struct_0(A_49) | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.73/1.43  tff(c_111, plain, (![A_52]: (u1_struct_0(A_52)=k2_struct_0(A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_56, c_105])).
% 2.73/1.43  tff(c_115, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_74, c_111])).
% 2.73/1.43  tff(c_194, plain, (![A_69]: (m1_subset_1('#skF_4'(A_69), k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.73/1.43  tff(c_200, plain, (m1_subset_1('#skF_4'('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_115, c_194])).
% 2.73/1.43  tff(c_203, plain, (m1_subset_1('#skF_4'('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_200])).
% 2.73/1.43  tff(c_204, plain, (m1_subset_1('#skF_4'('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_78, c_203])).
% 2.73/1.43  tff(c_8, plain, (![B_6, A_4]: (v1_xboole_0(B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_4)) | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.73/1.43  tff(c_220, plain, (v1_xboole_0('#skF_4'('#skF_5')) | ~v1_xboole_0(k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_204, c_8])).
% 2.73/1.43  tff(c_234, plain, (~v1_xboole_0(k2_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_220])).
% 2.73/1.43  tff(c_72, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.73/1.43  tff(c_117, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_72])).
% 2.73/1.43  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.73/1.43  tff(c_58, plain, (![A_30]: (v4_pre_topc(k2_struct_0(A_30), A_30) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.73/1.43  tff(c_152, plain, (![A_62]: (r2_hidden(u1_struct_0(A_62), u1_pre_topc(A_62)) | ~v2_pre_topc(A_62) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.73/1.43  tff(c_158, plain, (r2_hidden(k2_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_115, c_152])).
% 2.73/1.43  tff(c_161, plain, (r2_hidden(k2_struct_0('#skF_5'), u1_pre_topc('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_158])).
% 2.73/1.43  tff(c_4, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.73/1.43  tff(c_6, plain, (![A_3]: (m1_subset_1(k2_subset_1(A_3), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.43  tff(c_87, plain, (![A_3]: (m1_subset_1(A_3, k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.73/1.43  tff(c_289, plain, (![B_75, A_76]: (v3_pre_topc(B_75, A_76) | ~r2_hidden(B_75, u1_pre_topc(A_76)) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.73/1.43  tff(c_304, plain, (![A_77]: (v3_pre_topc(u1_struct_0(A_77), A_77) | ~r2_hidden(u1_struct_0(A_77), u1_pre_topc(A_77)) | ~l1_pre_topc(A_77))), inference(resolution, [status(thm)], [c_87, c_289])).
% 2.73/1.43  tff(c_316, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5') | ~r2_hidden(k2_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_115, c_304])).
% 2.73/1.43  tff(c_321, plain, (v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_161, c_115, c_316])).
% 2.73/1.43  tff(c_84, plain, (![D_44]: (v4_pre_topc(D_44, '#skF_5') | ~r2_hidden(D_44, '#skF_7') | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.73/1.43  tff(c_133, plain, (![D_55]: (v4_pre_topc(D_55, '#skF_5') | ~r2_hidden(D_55, '#skF_7') | ~m1_subset_1(D_55, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_84])).
% 2.73/1.43  tff(c_138, plain, (v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~r2_hidden(k2_struct_0('#skF_5'), '#skF_7')), inference(resolution, [status(thm)], [c_87, c_133])).
% 2.73/1.43  tff(c_166, plain, (~r2_hidden(k2_struct_0('#skF_5'), '#skF_7')), inference(splitLeft, [status(thm)], [c_138])).
% 2.73/1.43  tff(c_80, plain, (![D_44]: (r2_hidden(D_44, '#skF_7') | ~r2_hidden('#skF_6', D_44) | ~v4_pre_topc(D_44, '#skF_5') | ~v3_pre_topc(D_44, '#skF_5') | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_142])).
% 2.73/1.43  tff(c_222, plain, (![D_70]: (r2_hidden(D_70, '#skF_7') | ~r2_hidden('#skF_6', D_70) | ~v4_pre_topc(D_70, '#skF_5') | ~v3_pre_topc(D_70, '#skF_5') | ~m1_subset_1(D_70, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_80])).
% 2.73/1.43  tff(c_229, plain, (r2_hidden(k2_struct_0('#skF_5'), '#skF_7') | ~r2_hidden('#skF_6', k2_struct_0('#skF_5')) | ~v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_87, c_222])).
% 2.73/1.43  tff(c_233, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_5')) | ~v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_166, c_229])).
% 2.73/1.43  tff(c_386, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_5')) | ~v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_321, c_233])).
% 2.73/1.43  tff(c_387, plain, (~v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_386])).
% 2.73/1.43  tff(c_390, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_58, c_387])).
% 2.73/1.43  tff(c_394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_390])).
% 2.73/1.43  tff(c_395, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_386])).
% 2.73/1.43  tff(c_399, plain, (v1_xboole_0(k2_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_10, c_395])).
% 2.73/1.43  tff(c_402, plain, (v1_xboole_0(k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_399])).
% 2.73/1.43  tff(c_404, plain, $false, inference(negUnitSimplification, [status(thm)], [c_234, c_402])).
% 2.73/1.43  tff(c_405, plain, (v1_xboole_0('#skF_4'('#skF_5'))), inference(splitRight, [status(thm)], [c_220])).
% 2.73/1.43  tff(c_64, plain, (![A_31]: (~v1_xboole_0('#skF_4'(A_31)) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.73/1.43  tff(c_409, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_405, c_64])).
% 2.73/1.43  tff(c_412, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_409])).
% 2.73/1.43  tff(c_414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_412])).
% 2.73/1.43  tff(c_416, plain, (r2_hidden(k2_struct_0('#skF_5'), '#skF_7')), inference(splitRight, [status(thm)], [c_138])).
% 2.73/1.43  tff(c_12, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.73/1.43  tff(c_419, plain, (~r1_tarski('#skF_7', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_416, c_12])).
% 2.73/1.43  tff(c_423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_419])).
% 2.73/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.43  
% 2.73/1.43  Inference rules
% 2.73/1.43  ----------------------
% 2.73/1.43  #Ref     : 0
% 2.73/1.43  #Sup     : 59
% 2.73/1.43  #Fact    : 0
% 2.73/1.43  #Define  : 0
% 2.73/1.43  #Split   : 9
% 2.73/1.43  #Chain   : 0
% 2.73/1.43  #Close   : 0
% 2.73/1.43  
% 2.73/1.43  Ordering : KBO
% 2.73/1.43  
% 2.73/1.43  Simplification rules
% 2.73/1.43  ----------------------
% 2.73/1.43  #Subsume      : 10
% 2.73/1.43  #Demod        : 48
% 2.73/1.43  #Tautology    : 15
% 2.73/1.43  #SimpNegUnit  : 7
% 2.73/1.43  #BackRed      : 2
% 2.73/1.43  
% 2.73/1.43  #Partial instantiations: 0
% 2.73/1.43  #Strategies tried      : 1
% 2.73/1.43  
% 2.73/1.43  Timing (in seconds)
% 2.73/1.43  ----------------------
% 2.73/1.43  Preprocessing        : 0.37
% 2.73/1.43  Parsing              : 0.19
% 2.73/1.43  CNF conversion       : 0.03
% 2.73/1.43  Main loop            : 0.28
% 2.73/1.43  Inferencing          : 0.09
% 2.73/1.43  Reduction            : 0.09
% 2.73/1.43  Demodulation         : 0.07
% 2.73/1.43  BG Simplification    : 0.02
% 2.73/1.43  Subsumption          : 0.05
% 2.73/1.43  Abstraction          : 0.01
% 2.73/1.43  MUC search           : 0.00
% 2.73/1.43  Cooper               : 0.00
% 2.73/1.43  Total                : 0.69
% 2.73/1.43  Index Insertion      : 0.00
% 2.73/1.43  Index Deletion       : 0.00
% 2.73/1.43  Index Matching       : 0.00
% 2.73/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
