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
% DateTime   : Thu Dec  3 10:31:04 EST 2020

% Result     : Theorem 6.30s
% Output     : CNFRefutation 6.63s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 360 expanded)
%              Number of leaves         :   37 ( 134 expanded)
%              Depth                    :   14
%              Number of atoms          :  277 (1426 expanded)
%              Number of equality atoms :   24 ( 117 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k5_waybel_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k5_waybel_0,type,(
    k5_waybel_0: ( $i * $i ) > $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_155,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_yellow_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v2_waybel_0(B,A)
              & v13_waybel_0(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v1_subset_1(B,u1_struct_0(A))
            <=> ~ r2_hidden(k3_yellow_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                <=> r2_hidden(D,C) ) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k3_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r1_orders_2(A,k3_yellow_0(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k5_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_waybel_0)).

tff(f_119,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k5_waybel_0(A,B))
              <=> r1_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_waybel_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v13_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r1_orders_2(A,C,D) )
                     => r2_hidden(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

tff(c_14,plain,(
    ! [A_12] : ~ v1_subset_1('#skF_2'(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_12] : m1_subset_1('#skF_2'(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1093,plain,(
    ! [B_194,A_195] :
      ( v1_subset_1(B_194,A_195)
      | B_194 = A_195
      | ~ m1_subset_1(B_194,k1_zfmisc_1(A_195)) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1096,plain,(
    ! [A_12] :
      ( v1_subset_1('#skF_2'(A_12),A_12)
      | '#skF_2'(A_12) = A_12 ) ),
    inference(resolution,[status(thm)],[c_16,c_1093])).

tff(c_1102,plain,(
    ! [A_12] : '#skF_2'(A_12) = A_12 ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_1096])).

tff(c_1113,plain,(
    ! [A_12] : ~ v1_subset_1(A_12,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1102,c_14])).

tff(c_1112,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1102,c_16])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_4,plain,(
    ! [A_5,B_6,C_10] :
      ( m1_subset_1('#skF_1'(A_5,B_6,C_10),A_5)
      | C_10 = B_6
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,(
    v13_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_72,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_77,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_58,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_56,plain,(
    v1_yellow_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_54,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_66,plain,
    ( r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_78,plain,(
    ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_66])).

tff(c_79,plain,(
    ! [B_62,A_63] :
      ( v1_subset_1(B_62,A_63)
      | B_62 = A_63
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_85,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_79])).

tff(c_91,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_85])).

tff(c_20,plain,(
    ! [A_17] :
      ( m1_subset_1(k3_yellow_0(A_17),u1_struct_0(A_17))
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_108,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_20])).

tff(c_112,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_108])).

tff(c_22,plain,(
    ! [A_18,B_20] :
      ( r1_orders_2(A_18,k3_yellow_0(A_18),B_20)
      | ~ m1_subset_1(B_20,u1_struct_0(A_18))
      | ~ l1_orders_2(A_18)
      | ~ v1_yellow_0(A_18)
      | ~ v5_orders_2(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_190,plain,(
    ! [A_81,B_82] :
      ( m1_subset_1(k5_waybel_0(A_81,B_82),k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ m1_subset_1(B_82,u1_struct_0(A_81))
      | ~ l1_orders_2(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_200,plain,(
    ! [B_82] :
      ( m1_subset_1(k5_waybel_0('#skF_5',B_82),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_190])).

tff(c_205,plain,(
    ! [B_82] :
      ( m1_subset_1(k5_waybel_0('#skF_5',B_82),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1(B_82,'#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_91,c_200])).

tff(c_206,plain,(
    ! [B_82] :
      ( m1_subset_1(k5_waybel_0('#skF_5',B_82),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1(B_82,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_205])).

tff(c_388,plain,(
    ! [C_123,A_124,B_125] :
      ( r2_hidden(C_123,k5_waybel_0(A_124,B_125))
      | ~ r1_orders_2(A_124,C_123,B_125)
      | ~ m1_subset_1(C_123,u1_struct_0(A_124))
      | ~ m1_subset_1(B_125,u1_struct_0(A_124))
      | ~ l1_orders_2(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1051,plain,(
    ! [C_188,A_189,A_190,B_191] :
      ( r2_hidden(C_188,A_189)
      | ~ m1_subset_1(k5_waybel_0(A_190,B_191),k1_zfmisc_1(A_189))
      | ~ r1_orders_2(A_190,C_188,B_191)
      | ~ m1_subset_1(C_188,u1_struct_0(A_190))
      | ~ m1_subset_1(B_191,u1_struct_0(A_190))
      | ~ l1_orders_2(A_190)
      | v2_struct_0(A_190) ) ),
    inference(resolution,[status(thm)],[c_388,c_2])).

tff(c_1053,plain,(
    ! [C_188,B_82] :
      ( r2_hidden(C_188,'#skF_6')
      | ~ r1_orders_2('#skF_5',C_188,B_82)
      | ~ m1_subset_1(C_188,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_82,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(B_82,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_206,c_1051])).

tff(c_1061,plain,(
    ! [C_188,B_82] :
      ( r2_hidden(C_188,'#skF_6')
      | ~ r1_orders_2('#skF_5',C_188,B_82)
      | ~ m1_subset_1(C_188,'#skF_6')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(B_82,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_91,c_91,c_1053])).

tff(c_1065,plain,(
    ! [C_192,B_193] :
      ( r2_hidden(C_192,'#skF_6')
      | ~ r1_orders_2('#skF_5',C_192,B_193)
      | ~ m1_subset_1(C_192,'#skF_6')
      | ~ m1_subset_1(B_193,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1061])).

tff(c_1073,plain,(
    ! [B_20] :
      ( r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ m1_subset_1(B_20,'#skF_6')
      | ~ m1_subset_1(B_20,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v1_yellow_0('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_1065])).

tff(c_1079,plain,(
    ! [B_20] :
      ( r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ m1_subset_1(B_20,'#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_91,c_112,c_1073])).

tff(c_1080,plain,(
    ! [B_20] : ~ m1_subset_1(B_20,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_77,c_1079])).

tff(c_1088,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1080,c_112])).

tff(c_1090,plain,(
    r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_1105,plain,(
    ! [A_196,C_197,B_198] :
      ( m1_subset_1(A_196,C_197)
      | ~ m1_subset_1(B_198,k1_zfmisc_1(C_197))
      | ~ r2_hidden(A_196,B_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1111,plain,(
    ! [A_196] :
      ( m1_subset_1(A_196,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_196,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_1105])).

tff(c_1553,plain,(
    ! [D_285,B_286,A_287,C_288] :
      ( r2_hidden(D_285,B_286)
      | ~ r1_orders_2(A_287,C_288,D_285)
      | ~ r2_hidden(C_288,B_286)
      | ~ m1_subset_1(D_285,u1_struct_0(A_287))
      | ~ m1_subset_1(C_288,u1_struct_0(A_287))
      | ~ v13_waybel_0(B_286,A_287)
      | ~ m1_subset_1(B_286,k1_zfmisc_1(u1_struct_0(A_287)))
      | ~ l1_orders_2(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2558,plain,(
    ! [B_395,B_396,A_397] :
      ( r2_hidden(B_395,B_396)
      | ~ r2_hidden(k3_yellow_0(A_397),B_396)
      | ~ m1_subset_1(k3_yellow_0(A_397),u1_struct_0(A_397))
      | ~ v13_waybel_0(B_396,A_397)
      | ~ m1_subset_1(B_396,k1_zfmisc_1(u1_struct_0(A_397)))
      | ~ m1_subset_1(B_395,u1_struct_0(A_397))
      | ~ l1_orders_2(A_397)
      | ~ v1_yellow_0(A_397)
      | ~ v5_orders_2(A_397)
      | v2_struct_0(A_397) ) ),
    inference(resolution,[status(thm)],[c_22,c_1553])).

tff(c_2566,plain,(
    ! [B_395,B_396] :
      ( r2_hidden(B_395,B_396)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_396)
      | ~ v13_waybel_0(B_396,'#skF_5')
      | ~ m1_subset_1(B_396,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_395,u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ v1_yellow_0('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1111,c_2558])).

tff(c_2579,plain,(
    ! [B_395,B_396] :
      ( r2_hidden(B_395,B_396)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_396)
      | ~ v13_waybel_0(B_396,'#skF_5')
      | ~ m1_subset_1(B_396,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_395,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1090,c_58,c_56,c_54,c_2566])).

tff(c_2582,plain,(
    ! [B_398,B_399] :
      ( r2_hidden(B_398,B_399)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_399)
      | ~ v13_waybel_0(B_399,'#skF_5')
      | ~ m1_subset_1(B_399,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_398,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2579])).

tff(c_2623,plain,(
    ! [B_398] :
      ( r2_hidden(B_398,'#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ v13_waybel_0('#skF_6','#skF_5')
      | ~ m1_subset_1(B_398,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_46,c_2582])).

tff(c_2645,plain,(
    ! [B_400] :
      ( r2_hidden(B_400,'#skF_6')
      | ~ m1_subset_1(B_400,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1090,c_2623])).

tff(c_2960,plain,(
    ! [B_414,C_415] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_414,C_415),'#skF_6')
      | C_415 = B_414
      | ~ m1_subset_1(C_415,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1(B_414,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_4,c_2645])).

tff(c_1425,plain,(
    ! [A_263,B_264,C_265] :
      ( r2_hidden('#skF_1'(A_263,B_264,C_265),B_264)
      | r2_hidden('#skF_1'(A_263,B_264,C_265),C_265)
      | C_265 = B_264
      | ~ m1_subset_1(C_265,k1_zfmisc_1(A_263))
      | ~ m1_subset_1(B_264,k1_zfmisc_1(A_263)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1461,plain,(
    ! [A_263,B_264,C_265,A_1] :
      ( r2_hidden('#skF_1'(A_263,B_264,C_265),A_1)
      | ~ m1_subset_1(B_264,k1_zfmisc_1(A_1))
      | r2_hidden('#skF_1'(A_263,B_264,C_265),C_265)
      | C_265 = B_264
      | ~ m1_subset_1(C_265,k1_zfmisc_1(A_263))
      | ~ m1_subset_1(B_264,k1_zfmisc_1(A_263)) ) ),
    inference(resolution,[status(thm)],[c_1425,c_2])).

tff(c_2059,plain,(
    ! [B_356,A_357,A_358] :
      ( ~ m1_subset_1(B_356,k1_zfmisc_1(A_357))
      | B_356 = A_357
      | ~ m1_subset_1(A_357,k1_zfmisc_1(A_358))
      | ~ m1_subset_1(B_356,k1_zfmisc_1(A_358))
      | r2_hidden('#skF_1'(A_358,B_356,A_357),A_357) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1461])).

tff(c_6,plain,(
    ! [A_5,B_6,C_10] :
      ( ~ r2_hidden('#skF_1'(A_5,B_6,C_10),C_10)
      | ~ r2_hidden('#skF_1'(A_5,B_6,C_10),B_6)
      | C_10 = B_6
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2086,plain,(
    ! [A_358,B_356,A_357] :
      ( ~ r2_hidden('#skF_1'(A_358,B_356,A_357),B_356)
      | ~ m1_subset_1(B_356,k1_zfmisc_1(A_357))
      | B_356 = A_357
      | ~ m1_subset_1(A_357,k1_zfmisc_1(A_358))
      | ~ m1_subset_1(B_356,k1_zfmisc_1(A_358)) ) ),
    inference(resolution,[status(thm)],[c_2059,c_6])).

tff(c_2964,plain,(
    ! [C_415] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(C_415))
      | C_415 = '#skF_6'
      | ~ m1_subset_1(C_415,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_2960,c_2086])).

tff(c_2993,plain,(
    ! [C_419] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(C_419))
      | C_419 = '#skF_6'
      | ~ m1_subset_1(C_419,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2964])).

tff(c_3045,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1112,c_2993])).

tff(c_3066,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3045])).

tff(c_2171,plain,(
    ! [A_365,B_366,A_367,A_368] :
      ( r2_hidden('#skF_1'(A_365,B_366,A_367),A_368)
      | ~ m1_subset_1(A_367,k1_zfmisc_1(A_368))
      | ~ m1_subset_1(B_366,k1_zfmisc_1(A_367))
      | B_366 = A_367
      | ~ m1_subset_1(A_367,k1_zfmisc_1(A_365))
      | ~ m1_subset_1(B_366,k1_zfmisc_1(A_365)) ) ),
    inference(resolution,[status(thm)],[c_2059,c_2])).

tff(c_2213,plain,(
    ! [A_369,A_370,A_371] :
      ( ~ m1_subset_1(A_369,k1_zfmisc_1(A_370))
      | ~ m1_subset_1(A_370,k1_zfmisc_1(A_369))
      | A_370 = A_369
      | ~ m1_subset_1(A_369,k1_zfmisc_1(A_371))
      | ~ m1_subset_1(A_370,k1_zfmisc_1(A_371)) ) ),
    inference(resolution,[status(thm)],[c_2171,c_2086])).

tff(c_2261,plain,(
    ! [A_371] :
      ( ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6'))
      | u1_struct_0('#skF_5') = '#skF_6'
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_371))
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_371)) ) ),
    inference(resolution,[status(thm)],[c_46,c_2213])).

tff(c_2353,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2261])).

tff(c_3087,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3066,c_2353])).

tff(c_3107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1112,c_3087])).

tff(c_3109,plain,(
    m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2261])).

tff(c_3108,plain,(
    ! [A_371] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_371))
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_371))
      | u1_struct_0('#skF_5') = '#skF_6' ) ),
    inference(splitRight,[status(thm)],[c_2261])).

tff(c_3291,plain,(
    ! [A_424] :
      ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_424))
      | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(A_424)) ) ),
    inference(splitLeft,[status(thm)],[c_3108])).

tff(c_3294,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_3109,c_3291])).

tff(c_3302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1112,c_3294])).

tff(c_3303,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3108])).

tff(c_1089,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_3319,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3303,c_1089])).

tff(c_3325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1113,c_3319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.30/2.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.30/2.28  
% 6.30/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.30/2.28  %$ r1_orders_2 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k5_waybel_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_5 > #skF_6 > #skF_4
% 6.30/2.28  
% 6.30/2.28  %Foreground sorts:
% 6.30/2.28  
% 6.30/2.28  
% 6.30/2.28  %Background operators:
% 6.30/2.28  
% 6.30/2.28  
% 6.30/2.28  %Foreground operators:
% 6.30/2.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.30/2.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.30/2.28  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.30/2.28  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.30/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.30/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.30/2.28  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 6.30/2.28  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 6.30/2.28  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 6.30/2.28  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 6.30/2.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.30/2.28  tff('#skF_5', type, '#skF_5': $i).
% 6.30/2.28  tff('#skF_6', type, '#skF_6': $i).
% 6.30/2.28  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.30/2.28  tff(k5_waybel_0, type, k5_waybel_0: ($i * $i) > $i).
% 6.30/2.28  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.30/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.30/2.28  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.30/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.30/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.30/2.28  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 6.30/2.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.30/2.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.30/2.28  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.30/2.28  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 6.30/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.30/2.28  
% 6.63/2.30  tff(f_52, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 6.63/2.30  tff(f_126, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 6.63/2.30  tff(f_155, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_7)).
% 6.63/2.30  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 6.63/2.30  tff(f_62, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k3_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 6.63/2.30  tff(f_76, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r1_orders_2(A, k3_yellow_0(A), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_yellow_0)).
% 6.63/2.30  tff(f_104, axiom, (![A, B]: (((~v2_struct_0(A) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k5_waybel_0(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_waybel_0)).
% 6.63/2.30  tff(f_119, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k5_waybel_0(A, B)) <=> r1_orders_2(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_waybel_0)).
% 6.63/2.30  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 6.63/2.30  tff(f_58, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 6.63/2.30  tff(f_95, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_waybel_0)).
% 6.63/2.30  tff(c_14, plain, (![A_12]: (~v1_subset_1('#skF_2'(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.63/2.30  tff(c_16, plain, (![A_12]: (m1_subset_1('#skF_2'(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.63/2.30  tff(c_1093, plain, (![B_194, A_195]: (v1_subset_1(B_194, A_195) | B_194=A_195 | ~m1_subset_1(B_194, k1_zfmisc_1(A_195)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.63/2.30  tff(c_1096, plain, (![A_12]: (v1_subset_1('#skF_2'(A_12), A_12) | '#skF_2'(A_12)=A_12)), inference(resolution, [status(thm)], [c_16, c_1093])).
% 6.63/2.30  tff(c_1102, plain, (![A_12]: ('#skF_2'(A_12)=A_12)), inference(negUnitSimplification, [status(thm)], [c_14, c_1096])).
% 6.63/2.30  tff(c_1113, plain, (![A_12]: (~v1_subset_1(A_12, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_1102, c_14])).
% 6.63/2.30  tff(c_1112, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_1102, c_16])).
% 6.63/2.30  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.63/2.30  tff(c_4, plain, (![A_5, B_6, C_10]: (m1_subset_1('#skF_1'(A_5, B_6, C_10), A_5) | C_10=B_6 | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.63/2.30  tff(c_48, plain, (v13_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.63/2.30  tff(c_64, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.63/2.30  tff(c_72, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.63/2.30  tff(c_77, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_72])).
% 6.63/2.30  tff(c_58, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.63/2.30  tff(c_56, plain, (v1_yellow_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.63/2.30  tff(c_54, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.63/2.30  tff(c_66, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.63/2.30  tff(c_78, plain, (~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_77, c_66])).
% 6.63/2.30  tff(c_79, plain, (![B_62, A_63]: (v1_subset_1(B_62, A_63) | B_62=A_63 | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.63/2.30  tff(c_85, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_46, c_79])).
% 6.63/2.30  tff(c_91, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_78, c_85])).
% 6.63/2.30  tff(c_20, plain, (![A_17]: (m1_subset_1(k3_yellow_0(A_17), u1_struct_0(A_17)) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.63/2.30  tff(c_108, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6') | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_91, c_20])).
% 6.63/2.30  tff(c_112, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_108])).
% 6.63/2.30  tff(c_22, plain, (![A_18, B_20]: (r1_orders_2(A_18, k3_yellow_0(A_18), B_20) | ~m1_subset_1(B_20, u1_struct_0(A_18)) | ~l1_orders_2(A_18) | ~v1_yellow_0(A_18) | ~v5_orders_2(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.63/2.30  tff(c_190, plain, (![A_81, B_82]: (m1_subset_1(k5_waybel_0(A_81, B_82), k1_zfmisc_1(u1_struct_0(A_81))) | ~m1_subset_1(B_82, u1_struct_0(A_81)) | ~l1_orders_2(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.63/2.30  tff(c_200, plain, (![B_82]: (m1_subset_1(k5_waybel_0('#skF_5', B_82), k1_zfmisc_1('#skF_6')) | ~m1_subset_1(B_82, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_91, c_190])).
% 6.63/2.30  tff(c_205, plain, (![B_82]: (m1_subset_1(k5_waybel_0('#skF_5', B_82), k1_zfmisc_1('#skF_6')) | ~m1_subset_1(B_82, '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_91, c_200])).
% 6.63/2.30  tff(c_206, plain, (![B_82]: (m1_subset_1(k5_waybel_0('#skF_5', B_82), k1_zfmisc_1('#skF_6')) | ~m1_subset_1(B_82, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_205])).
% 6.63/2.30  tff(c_388, plain, (![C_123, A_124, B_125]: (r2_hidden(C_123, k5_waybel_0(A_124, B_125)) | ~r1_orders_2(A_124, C_123, B_125) | ~m1_subset_1(C_123, u1_struct_0(A_124)) | ~m1_subset_1(B_125, u1_struct_0(A_124)) | ~l1_orders_2(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.63/2.30  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.63/2.30  tff(c_1051, plain, (![C_188, A_189, A_190, B_191]: (r2_hidden(C_188, A_189) | ~m1_subset_1(k5_waybel_0(A_190, B_191), k1_zfmisc_1(A_189)) | ~r1_orders_2(A_190, C_188, B_191) | ~m1_subset_1(C_188, u1_struct_0(A_190)) | ~m1_subset_1(B_191, u1_struct_0(A_190)) | ~l1_orders_2(A_190) | v2_struct_0(A_190))), inference(resolution, [status(thm)], [c_388, c_2])).
% 6.63/2.30  tff(c_1053, plain, (![C_188, B_82]: (r2_hidden(C_188, '#skF_6') | ~r1_orders_2('#skF_5', C_188, B_82) | ~m1_subset_1(C_188, u1_struct_0('#skF_5')) | ~m1_subset_1(B_82, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~m1_subset_1(B_82, '#skF_6'))), inference(resolution, [status(thm)], [c_206, c_1051])).
% 6.63/2.30  tff(c_1061, plain, (![C_188, B_82]: (r2_hidden(C_188, '#skF_6') | ~r1_orders_2('#skF_5', C_188, B_82) | ~m1_subset_1(C_188, '#skF_6') | v2_struct_0('#skF_5') | ~m1_subset_1(B_82, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_91, c_91, c_1053])).
% 6.63/2.30  tff(c_1065, plain, (![C_192, B_193]: (r2_hidden(C_192, '#skF_6') | ~r1_orders_2('#skF_5', C_192, B_193) | ~m1_subset_1(C_192, '#skF_6') | ~m1_subset_1(B_193, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_1061])).
% 6.63/2.30  tff(c_1073, plain, (![B_20]: (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6') | ~m1_subset_1(B_20, '#skF_6') | ~m1_subset_1(B_20, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_22, c_1065])).
% 6.63/2.30  tff(c_1079, plain, (![B_20]: (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~m1_subset_1(B_20, '#skF_6') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_91, c_112, c_1073])).
% 6.63/2.30  tff(c_1080, plain, (![B_20]: (~m1_subset_1(B_20, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_77, c_1079])).
% 6.63/2.30  tff(c_1088, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1080, c_112])).
% 6.63/2.30  tff(c_1090, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_72])).
% 6.63/2.30  tff(c_1105, plain, (![A_196, C_197, B_198]: (m1_subset_1(A_196, C_197) | ~m1_subset_1(B_198, k1_zfmisc_1(C_197)) | ~r2_hidden(A_196, B_198))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.63/2.30  tff(c_1111, plain, (![A_196]: (m1_subset_1(A_196, u1_struct_0('#skF_5')) | ~r2_hidden(A_196, '#skF_6'))), inference(resolution, [status(thm)], [c_46, c_1105])).
% 6.63/2.30  tff(c_1553, plain, (![D_285, B_286, A_287, C_288]: (r2_hidden(D_285, B_286) | ~r1_orders_2(A_287, C_288, D_285) | ~r2_hidden(C_288, B_286) | ~m1_subset_1(D_285, u1_struct_0(A_287)) | ~m1_subset_1(C_288, u1_struct_0(A_287)) | ~v13_waybel_0(B_286, A_287) | ~m1_subset_1(B_286, k1_zfmisc_1(u1_struct_0(A_287))) | ~l1_orders_2(A_287))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.63/2.30  tff(c_2558, plain, (![B_395, B_396, A_397]: (r2_hidden(B_395, B_396) | ~r2_hidden(k3_yellow_0(A_397), B_396) | ~m1_subset_1(k3_yellow_0(A_397), u1_struct_0(A_397)) | ~v13_waybel_0(B_396, A_397) | ~m1_subset_1(B_396, k1_zfmisc_1(u1_struct_0(A_397))) | ~m1_subset_1(B_395, u1_struct_0(A_397)) | ~l1_orders_2(A_397) | ~v1_yellow_0(A_397) | ~v5_orders_2(A_397) | v2_struct_0(A_397))), inference(resolution, [status(thm)], [c_22, c_1553])).
% 6.63/2.30  tff(c_2566, plain, (![B_395, B_396]: (r2_hidden(B_395, B_396) | ~r2_hidden(k3_yellow_0('#skF_5'), B_396) | ~v13_waybel_0(B_396, '#skF_5') | ~m1_subset_1(B_396, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_395, u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_1111, c_2558])).
% 6.63/2.30  tff(c_2579, plain, (![B_395, B_396]: (r2_hidden(B_395, B_396) | ~r2_hidden(k3_yellow_0('#skF_5'), B_396) | ~v13_waybel_0(B_396, '#skF_5') | ~m1_subset_1(B_396, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_395, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1090, c_58, c_56, c_54, c_2566])).
% 6.63/2.30  tff(c_2582, plain, (![B_398, B_399]: (r2_hidden(B_398, B_399) | ~r2_hidden(k3_yellow_0('#skF_5'), B_399) | ~v13_waybel_0(B_399, '#skF_5') | ~m1_subset_1(B_399, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_398, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_2579])).
% 6.63/2.30  tff(c_2623, plain, (![B_398]: (r2_hidden(B_398, '#skF_6') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | ~m1_subset_1(B_398, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_46, c_2582])).
% 6.63/2.30  tff(c_2645, plain, (![B_400]: (r2_hidden(B_400, '#skF_6') | ~m1_subset_1(B_400, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1090, c_2623])).
% 6.63/2.30  tff(c_2960, plain, (![B_414, C_415]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_414, C_415), '#skF_6') | C_415=B_414 | ~m1_subset_1(C_415, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(B_414, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_4, c_2645])).
% 6.63/2.30  tff(c_1425, plain, (![A_263, B_264, C_265]: (r2_hidden('#skF_1'(A_263, B_264, C_265), B_264) | r2_hidden('#skF_1'(A_263, B_264, C_265), C_265) | C_265=B_264 | ~m1_subset_1(C_265, k1_zfmisc_1(A_263)) | ~m1_subset_1(B_264, k1_zfmisc_1(A_263)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.63/2.30  tff(c_1461, plain, (![A_263, B_264, C_265, A_1]: (r2_hidden('#skF_1'(A_263, B_264, C_265), A_1) | ~m1_subset_1(B_264, k1_zfmisc_1(A_1)) | r2_hidden('#skF_1'(A_263, B_264, C_265), C_265) | C_265=B_264 | ~m1_subset_1(C_265, k1_zfmisc_1(A_263)) | ~m1_subset_1(B_264, k1_zfmisc_1(A_263)))), inference(resolution, [status(thm)], [c_1425, c_2])).
% 6.63/2.30  tff(c_2059, plain, (![B_356, A_357, A_358]: (~m1_subset_1(B_356, k1_zfmisc_1(A_357)) | B_356=A_357 | ~m1_subset_1(A_357, k1_zfmisc_1(A_358)) | ~m1_subset_1(B_356, k1_zfmisc_1(A_358)) | r2_hidden('#skF_1'(A_358, B_356, A_357), A_357))), inference(factorization, [status(thm), theory('equality')], [c_1461])).
% 6.63/2.30  tff(c_6, plain, (![A_5, B_6, C_10]: (~r2_hidden('#skF_1'(A_5, B_6, C_10), C_10) | ~r2_hidden('#skF_1'(A_5, B_6, C_10), B_6) | C_10=B_6 | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.63/2.30  tff(c_2086, plain, (![A_358, B_356, A_357]: (~r2_hidden('#skF_1'(A_358, B_356, A_357), B_356) | ~m1_subset_1(B_356, k1_zfmisc_1(A_357)) | B_356=A_357 | ~m1_subset_1(A_357, k1_zfmisc_1(A_358)) | ~m1_subset_1(B_356, k1_zfmisc_1(A_358)))), inference(resolution, [status(thm)], [c_2059, c_6])).
% 6.63/2.30  tff(c_2964, plain, (![C_415]: (~m1_subset_1('#skF_6', k1_zfmisc_1(C_415)) | C_415='#skF_6' | ~m1_subset_1(C_415, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_2960, c_2086])).
% 6.63/2.30  tff(c_2993, plain, (![C_419]: (~m1_subset_1('#skF_6', k1_zfmisc_1(C_419)) | C_419='#skF_6' | ~m1_subset_1(C_419, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2964])).
% 6.63/2.30  tff(c_3045, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_1112, c_2993])).
% 6.63/2.30  tff(c_3066, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3045])).
% 6.63/2.30  tff(c_2171, plain, (![A_365, B_366, A_367, A_368]: (r2_hidden('#skF_1'(A_365, B_366, A_367), A_368) | ~m1_subset_1(A_367, k1_zfmisc_1(A_368)) | ~m1_subset_1(B_366, k1_zfmisc_1(A_367)) | B_366=A_367 | ~m1_subset_1(A_367, k1_zfmisc_1(A_365)) | ~m1_subset_1(B_366, k1_zfmisc_1(A_365)))), inference(resolution, [status(thm)], [c_2059, c_2])).
% 6.63/2.30  tff(c_2213, plain, (![A_369, A_370, A_371]: (~m1_subset_1(A_369, k1_zfmisc_1(A_370)) | ~m1_subset_1(A_370, k1_zfmisc_1(A_369)) | A_370=A_369 | ~m1_subset_1(A_369, k1_zfmisc_1(A_371)) | ~m1_subset_1(A_370, k1_zfmisc_1(A_371)))), inference(resolution, [status(thm)], [c_2171, c_2086])).
% 6.63/2.30  tff(c_2261, plain, (![A_371]: (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6')) | u1_struct_0('#skF_5')='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_371)) | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_371)))), inference(resolution, [status(thm)], [c_46, c_2213])).
% 6.63/2.30  tff(c_2353, plain, (~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_2261])).
% 6.63/2.30  tff(c_3087, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_3066, c_2353])).
% 6.63/2.30  tff(c_3107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1112, c_3087])).
% 6.63/2.30  tff(c_3109, plain, (m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1('#skF_6'))), inference(splitRight, [status(thm)], [c_2261])).
% 6.63/2.30  tff(c_3108, plain, (![A_371]: (~m1_subset_1('#skF_6', k1_zfmisc_1(A_371)) | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_371)) | u1_struct_0('#skF_5')='#skF_6')), inference(splitRight, [status(thm)], [c_2261])).
% 6.63/2.30  tff(c_3291, plain, (![A_424]: (~m1_subset_1('#skF_6', k1_zfmisc_1(A_424)) | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(A_424)))), inference(splitLeft, [status(thm)], [c_3108])).
% 6.63/2.30  tff(c_3294, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(resolution, [status(thm)], [c_3109, c_3291])).
% 6.63/2.30  tff(c_3302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1112, c_3294])).
% 6.63/2.30  tff(c_3303, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_3108])).
% 6.63/2.30  tff(c_1089, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_72])).
% 6.63/2.30  tff(c_3319, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3303, c_1089])).
% 6.63/2.30  tff(c_3325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1113, c_3319])).
% 6.63/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.63/2.30  
% 6.63/2.30  Inference rules
% 6.63/2.30  ----------------------
% 6.63/2.30  #Ref     : 0
% 6.63/2.30  #Sup     : 647
% 6.63/2.30  #Fact    : 12
% 6.63/2.30  #Define  : 0
% 6.63/2.30  #Split   : 8
% 6.63/2.30  #Chain   : 0
% 6.63/2.30  #Close   : 0
% 6.63/2.30  
% 6.63/2.30  Ordering : KBO
% 6.63/2.30  
% 6.63/2.30  Simplification rules
% 6.63/2.30  ----------------------
% 6.63/2.30  #Subsume      : 82
% 6.63/2.30  #Demod        : 270
% 6.63/2.30  #Tautology    : 77
% 6.63/2.30  #SimpNegUnit  : 46
% 6.63/2.30  #BackRed      : 77
% 6.63/2.30  
% 6.63/2.30  #Partial instantiations: 0
% 6.63/2.30  #Strategies tried      : 1
% 6.63/2.30  
% 6.63/2.30  Timing (in seconds)
% 6.63/2.30  ----------------------
% 6.63/2.31  Preprocessing        : 0.34
% 6.63/2.31  Parsing              : 0.18
% 6.63/2.31  CNF conversion       : 0.03
% 6.63/2.31  Main loop            : 1.18
% 6.63/2.31  Inferencing          : 0.42
% 6.63/2.31  Reduction            : 0.31
% 6.63/2.31  Demodulation         : 0.20
% 6.63/2.31  BG Simplification    : 0.05
% 6.63/2.31  Subsumption          : 0.30
% 6.63/2.31  Abstraction          : 0.07
% 6.63/2.31  MUC search           : 0.00
% 6.63/2.31  Cooper               : 0.00
% 6.63/2.31  Total                : 1.57
% 6.63/2.31  Index Insertion      : 0.00
% 6.63/2.31  Index Deletion       : 0.00
% 6.63/2.31  Index Matching       : 0.00
% 6.63/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
