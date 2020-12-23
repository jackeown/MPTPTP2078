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
% DateTime   : Thu Dec  3 10:24:19 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 300 expanded)
%              Number of leaves         :   41 ( 121 expanded)
%              Depth                    :   12
%              Number of atoms          :  161 ( 869 expanded)
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

tff(f_140,negated_conjecture,(
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

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc7_pre_topc)).

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

tff(c_66,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_86,plain,(
    ! [A_1] : r1_tarski('#skF_7',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_74,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_72,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_56,plain,(
    ! [A_29] :
      ( l1_struct_0(A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_103,plain,(
    ! [A_49] :
      ( u1_struct_0(A_49) = k2_struct_0(A_49)
      | ~ l1_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_109,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = k2_struct_0(A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_56,c_103])).

tff(c_113,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_109])).

tff(c_191,plain,(
    ! [A_68] :
      ( m1_subset_1('#skF_4'(A_68),k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_197,plain,
    ( m1_subset_1('#skF_4'('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_191])).

tff(c_200,plain,
    ( m1_subset_1('#skF_4'('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_197])).

tff(c_201,plain,(
    m1_subset_1('#skF_4'('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_200])).

tff(c_8,plain,(
    ! [B_6,A_4] :
      ( v1_xboole_0(B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_4))
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_217,plain,
    ( v1_xboole_0('#skF_4'('#skF_5'))
    | ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_201,c_8])).

tff(c_218,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_115,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_70])).

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

tff(c_150,plain,(
    ! [A_62] :
      ( r2_hidden(u1_struct_0(A_62),u1_pre_topc(A_62))
      | ~ v2_pre_topc(A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_156,plain,
    ( r2_hidden(k2_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_150])).

tff(c_159,plain,(
    r2_hidden(k2_struct_0('#skF_5'),u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_74,c_156])).

tff(c_4,plain,(
    ! [A_2] : k2_subset_1(A_2) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k2_subset_1(A_3),k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    ! [A_3] : m1_subset_1(A_3,k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_237,plain,(
    ! [B_70,A_71] :
      ( v3_pre_topc(B_70,A_71)
      | ~ r2_hidden(B_70,u1_pre_topc(A_71))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_252,plain,(
    ! [A_72] :
      ( v3_pre_topc(u1_struct_0(A_72),A_72)
      | ~ r2_hidden(u1_struct_0(A_72),u1_pre_topc(A_72))
      | ~ l1_pre_topc(A_72) ) ),
    inference(resolution,[status(thm)],[c_85,c_237])).

tff(c_261,plain,
    ( v3_pre_topc(u1_struct_0('#skF_5'),'#skF_5')
    | ~ r2_hidden(k2_struct_0('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_252])).

tff(c_265,plain,(
    v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_159,c_113,c_261])).

tff(c_82,plain,(
    ! [D_44] :
      ( v4_pre_topc(D_44,'#skF_5')
      | ~ r2_hidden(D_44,'#skF_7')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_136,plain,(
    ! [D_58] :
      ( v4_pre_topc(D_58,'#skF_5')
      | ~ r2_hidden(D_58,'#skF_7')
      | ~ m1_subset_1(D_58,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_82])).

tff(c_141,plain,
    ( v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ r2_hidden(k2_struct_0('#skF_5'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_85,c_136])).

tff(c_164,plain,(
    ~ r2_hidden(k2_struct_0('#skF_5'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_78,plain,(
    ! [D_44] :
      ( r2_hidden(D_44,'#skF_7')
      | ~ r2_hidden('#skF_6',D_44)
      | ~ v4_pre_topc(D_44,'#skF_5')
      | ~ v3_pre_topc(D_44,'#skF_5')
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_220,plain,(
    ! [D_69] :
      ( r2_hidden(D_69,'#skF_7')
      | ~ r2_hidden('#skF_6',D_69)
      | ~ v4_pre_topc(D_69,'#skF_5')
      | ~ v3_pre_topc(D_69,'#skF_5')
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_78])).

tff(c_227,plain,
    ( r2_hidden(k2_struct_0('#skF_5'),'#skF_7')
    | ~ r2_hidden('#skF_6',k2_struct_0('#skF_5'))
    | ~ v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_85,c_220])).

tff(c_231,plain,
    ( ~ r2_hidden('#skF_6',k2_struct_0('#skF_5'))
    | ~ v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5')
    | ~ v3_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_227])).

tff(c_349,plain,
    ( ~ r2_hidden('#skF_6',k2_struct_0('#skF_5'))
    | ~ v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_265,c_231])).

tff(c_350,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_349])).

tff(c_353,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_350])).

tff(c_357,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_353])).

tff(c_358,plain,(
    ~ r2_hidden('#skF_6',k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_362,plain,
    ( v1_xboole_0(k2_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_10,c_358])).

tff(c_365,plain,(
    v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_362])).

tff(c_367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_365])).

tff(c_368,plain,(
    v1_xboole_0('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_62,plain,(
    ! [A_31] :
      ( ~ v1_xboole_0('#skF_4'(A_31))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_372,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_368,c_62])).

tff(c_375,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_372])).

tff(c_377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_375])).

tff(c_379,plain,(
    r2_hidden(k2_struct_0('#skF_5'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_383,plain,(
    ~ r1_tarski('#skF_7',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_379,c_12])).

tff(c_387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_383])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n020.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 20:47:22 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.30  
% 2.49/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.30  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3
% 2.49/1.30  
% 2.49/1.30  %Foreground sorts:
% 2.49/1.30  
% 2.49/1.30  
% 2.49/1.30  %Background operators:
% 2.49/1.30  
% 2.49/1.30  
% 2.49/1.30  %Foreground operators:
% 2.49/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.49/1.30  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.49/1.30  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.49/1.30  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.49/1.30  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.49/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.30  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.49/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.30  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.49/1.30  tff('#skF_7', type, '#skF_7': $i).
% 2.49/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.49/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.49/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.30  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.49/1.30  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.49/1.30  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.49/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.30  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.49/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.30  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.49/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.49/1.30  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.49/1.30  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.49/1.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.49/1.30  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.49/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.30  
% 2.49/1.32  tff(f_140, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.49/1.32  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.49/1.32  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.49/1.32  tff(f_78, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.49/1.32  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc7_pre_topc)).
% 2.49/1.32  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.49/1.32  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.49/1.32  tff(f_97, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.49/1.32  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 2.49/1.32  tff(f_29, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.49/1.32  tff(f_31, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.49/1.32  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.49/1.32  tff(f_49, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.49/1.32  tff(c_66, plain, (k1_xboole_0='#skF_7'), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.49/1.32  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.49/1.32  tff(c_86, plain, (![A_1]: (r1_tarski('#skF_7', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2])).
% 2.49/1.32  tff(c_76, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.49/1.32  tff(c_74, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.49/1.32  tff(c_72, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.49/1.32  tff(c_56, plain, (![A_29]: (l1_struct_0(A_29) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.49/1.32  tff(c_103, plain, (![A_49]: (u1_struct_0(A_49)=k2_struct_0(A_49) | ~l1_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.49/1.32  tff(c_109, plain, (![A_52]: (u1_struct_0(A_52)=k2_struct_0(A_52) | ~l1_pre_topc(A_52))), inference(resolution, [status(thm)], [c_56, c_103])).
% 2.49/1.32  tff(c_113, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_72, c_109])).
% 2.49/1.32  tff(c_191, plain, (![A_68]: (m1_subset_1('#skF_4'(A_68), k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.49/1.32  tff(c_197, plain, (m1_subset_1('#skF_4'('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_113, c_191])).
% 2.49/1.32  tff(c_200, plain, (m1_subset_1('#skF_4'('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_197])).
% 2.49/1.32  tff(c_201, plain, (m1_subset_1('#skF_4'('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_76, c_200])).
% 2.49/1.32  tff(c_8, plain, (![B_6, A_4]: (v1_xboole_0(B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(A_4)) | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.49/1.32  tff(c_217, plain, (v1_xboole_0('#skF_4'('#skF_5')) | ~v1_xboole_0(k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_201, c_8])).
% 2.49/1.32  tff(c_218, plain, (~v1_xboole_0(k2_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_217])).
% 2.49/1.32  tff(c_70, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.49/1.32  tff(c_115, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_70])).
% 2.49/1.32  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.49/1.32  tff(c_58, plain, (![A_30]: (v4_pre_topc(k2_struct_0(A_30), A_30) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.49/1.32  tff(c_150, plain, (![A_62]: (r2_hidden(u1_struct_0(A_62), u1_pre_topc(A_62)) | ~v2_pre_topc(A_62) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.49/1.32  tff(c_156, plain, (r2_hidden(k2_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_113, c_150])).
% 2.49/1.32  tff(c_159, plain, (r2_hidden(k2_struct_0('#skF_5'), u1_pre_topc('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_74, c_156])).
% 2.49/1.32  tff(c_4, plain, (![A_2]: (k2_subset_1(A_2)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.49/1.32  tff(c_6, plain, (![A_3]: (m1_subset_1(k2_subset_1(A_3), k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.49/1.32  tff(c_85, plain, (![A_3]: (m1_subset_1(A_3, k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.49/1.32  tff(c_237, plain, (![B_70, A_71]: (v3_pre_topc(B_70, A_71) | ~r2_hidden(B_70, u1_pre_topc(A_71)) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.49/1.32  tff(c_252, plain, (![A_72]: (v3_pre_topc(u1_struct_0(A_72), A_72) | ~r2_hidden(u1_struct_0(A_72), u1_pre_topc(A_72)) | ~l1_pre_topc(A_72))), inference(resolution, [status(thm)], [c_85, c_237])).
% 2.49/1.32  tff(c_261, plain, (v3_pre_topc(u1_struct_0('#skF_5'), '#skF_5') | ~r2_hidden(k2_struct_0('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_113, c_252])).
% 2.49/1.32  tff(c_265, plain, (v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_159, c_113, c_261])).
% 2.49/1.32  tff(c_82, plain, (![D_44]: (v4_pre_topc(D_44, '#skF_5') | ~r2_hidden(D_44, '#skF_7') | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.49/1.32  tff(c_136, plain, (![D_58]: (v4_pre_topc(D_58, '#skF_5') | ~r2_hidden(D_58, '#skF_7') | ~m1_subset_1(D_58, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_82])).
% 2.49/1.32  tff(c_141, plain, (v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~r2_hidden(k2_struct_0('#skF_5'), '#skF_7')), inference(resolution, [status(thm)], [c_85, c_136])).
% 2.49/1.32  tff(c_164, plain, (~r2_hidden(k2_struct_0('#skF_5'), '#skF_7')), inference(splitLeft, [status(thm)], [c_141])).
% 2.49/1.32  tff(c_78, plain, (![D_44]: (r2_hidden(D_44, '#skF_7') | ~r2_hidden('#skF_6', D_44) | ~v4_pre_topc(D_44, '#skF_5') | ~v3_pre_topc(D_44, '#skF_5') | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 2.49/1.32  tff(c_220, plain, (![D_69]: (r2_hidden(D_69, '#skF_7') | ~r2_hidden('#skF_6', D_69) | ~v4_pre_topc(D_69, '#skF_5') | ~v3_pre_topc(D_69, '#skF_5') | ~m1_subset_1(D_69, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_78])).
% 2.49/1.32  tff(c_227, plain, (r2_hidden(k2_struct_0('#skF_5'), '#skF_7') | ~r2_hidden('#skF_6', k2_struct_0('#skF_5')) | ~v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_85, c_220])).
% 2.49/1.32  tff(c_231, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_5')) | ~v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5') | ~v3_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_164, c_227])).
% 2.49/1.32  tff(c_349, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_5')) | ~v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_265, c_231])).
% 2.49/1.32  tff(c_350, plain, (~v4_pre_topc(k2_struct_0('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_349])).
% 2.49/1.32  tff(c_353, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_58, c_350])).
% 2.49/1.32  tff(c_357, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_353])).
% 2.49/1.32  tff(c_358, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_349])).
% 2.49/1.32  tff(c_362, plain, (v1_xboole_0(k2_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_10, c_358])).
% 2.49/1.32  tff(c_365, plain, (v1_xboole_0(k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_362])).
% 2.49/1.32  tff(c_367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_365])).
% 2.49/1.32  tff(c_368, plain, (v1_xboole_0('#skF_4'('#skF_5'))), inference(splitRight, [status(thm)], [c_217])).
% 2.49/1.32  tff(c_62, plain, (![A_31]: (~v1_xboole_0('#skF_4'(A_31)) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.49/1.32  tff(c_372, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_368, c_62])).
% 2.49/1.32  tff(c_375, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_372])).
% 2.49/1.32  tff(c_377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_375])).
% 2.49/1.32  tff(c_379, plain, (r2_hidden(k2_struct_0('#skF_5'), '#skF_7')), inference(splitRight, [status(thm)], [c_141])).
% 2.49/1.32  tff(c_12, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.49/1.32  tff(c_383, plain, (~r1_tarski('#skF_7', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_379, c_12])).
% 2.49/1.32  tff(c_387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_383])).
% 2.49/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.32  
% 2.49/1.32  Inference rules
% 2.49/1.32  ----------------------
% 2.49/1.32  #Ref     : 0
% 2.49/1.32  #Sup     : 53
% 2.49/1.32  #Fact    : 0
% 2.49/1.32  #Define  : 0
% 2.49/1.32  #Split   : 8
% 2.49/1.32  #Chain   : 0
% 2.49/1.32  #Close   : 0
% 2.49/1.32  
% 2.49/1.32  Ordering : KBO
% 2.49/1.32  
% 2.49/1.32  Simplification rules
% 2.49/1.32  ----------------------
% 2.49/1.32  #Subsume      : 10
% 2.49/1.32  #Demod        : 42
% 2.49/1.32  #Tautology    : 12
% 2.49/1.32  #SimpNegUnit  : 8
% 2.49/1.32  #BackRed      : 2
% 2.49/1.32  
% 2.49/1.32  #Partial instantiations: 0
% 2.49/1.32  #Strategies tried      : 1
% 2.49/1.32  
% 2.49/1.32  Timing (in seconds)
% 2.49/1.32  ----------------------
% 2.49/1.32  Preprocessing        : 0.33
% 2.49/1.32  Parsing              : 0.17
% 2.49/1.32  CNF conversion       : 0.03
% 2.49/1.32  Main loop            : 0.23
% 2.49/1.32  Inferencing          : 0.07
% 2.49/1.32  Reduction            : 0.08
% 2.49/1.32  Demodulation         : 0.05
% 2.49/1.32  BG Simplification    : 0.02
% 2.49/1.32  Subsumption          : 0.04
% 2.49/1.32  Abstraction          : 0.01
% 2.49/1.32  MUC search           : 0.00
% 2.49/1.32  Cooper               : 0.00
% 2.49/1.32  Total                : 0.60
% 2.49/1.32  Index Insertion      : 0.00
% 2.49/1.32  Index Deletion       : 0.00
% 2.49/1.32  Index Matching       : 0.00
% 2.49/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
