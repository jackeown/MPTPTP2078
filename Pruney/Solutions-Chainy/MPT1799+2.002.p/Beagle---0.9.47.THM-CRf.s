%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:57 EST 2020

% Result     : Theorem 8.24s
% Output     : CNFRefutation 8.24s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 337 expanded)
%              Number of leaves         :   31 ( 134 expanded)
%              Depth                    :   22
%              Number of atoms          :  280 (1619 expanded)
%              Number of equality atoms :   21 ( 145 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tsep_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > k5_tmap_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_164,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( m1_pre_topc(C,k8_tmap_1(A,B))
               => ( u1_struct_0(C) = u1_struct_0(B)
                 => ( v1_tsep_1(C,k8_tmap_1(A,B))
                    & m1_pre_topc(C,k8_tmap_1(A,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_tmap_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( ( v1_pre_topc(C)
                & v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( C = k8_tmap_1(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( D = u1_struct_0(B)
                     => C = k6_tmap_1(A,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_tmap_1)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
            & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_102,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r2_hidden(B,k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_134,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(c_44,plain,(
    m1_pre_topc('#skF_4',k8_tmap_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_40,plain,
    ( ~ m1_pre_topc('#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v1_tsep_1('#skF_4',k8_tmap_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_56,plain,(
    ~ v1_tsep_1('#skF_4',k8_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_20,plain,(
    ! [A_28,B_29] :
      ( l1_pre_topc(k8_tmap_1(A_28,B_29))
      | ~ m1_pre_topc(B_29,A_28)
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [A_28,B_29] :
      ( v1_pre_topc(k8_tmap_1(A_28,B_29))
      | ~ m1_pre_topc(B_29,A_28)
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22,plain,(
    ! [A_28,B_29] :
      ( v2_pre_topc(k8_tmap_1(A_28,B_29))
      | ~ m1_pre_topc(B_29,A_28)
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28)
      | v2_struct_0(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_38,plain,(
    ! [B_45,A_43] :
      ( m1_subset_1(u1_struct_0(B_45),k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_770,plain,(
    ! [A_163,B_164] :
      ( k6_tmap_1(A_163,u1_struct_0(B_164)) = k8_tmap_1(A_163,B_164)
      | ~ m1_subset_1(u1_struct_0(B_164),k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_pre_topc(k8_tmap_1(A_163,B_164))
      | ~ v2_pre_topc(k8_tmap_1(A_163,B_164))
      | ~ v1_pre_topc(k8_tmap_1(A_163,B_164))
      | ~ m1_pre_topc(B_164,A_163)
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1010,plain,(
    ! [A_178,B_179] :
      ( k6_tmap_1(A_178,u1_struct_0(B_179)) = k8_tmap_1(A_178,B_179)
      | ~ l1_pre_topc(k8_tmap_1(A_178,B_179))
      | ~ v2_pre_topc(k8_tmap_1(A_178,B_179))
      | ~ v1_pre_topc(k8_tmap_1(A_178,B_179))
      | ~ v2_pre_topc(A_178)
      | v2_struct_0(A_178)
      | ~ m1_pre_topc(B_179,A_178)
      | ~ l1_pre_topc(A_178) ) ),
    inference(resolution,[status(thm)],[c_38,c_770])).

tff(c_1015,plain,(
    ! [A_180,B_181] :
      ( k6_tmap_1(A_180,u1_struct_0(B_181)) = k8_tmap_1(A_180,B_181)
      | ~ l1_pre_topc(k8_tmap_1(A_180,B_181))
      | ~ v1_pre_topc(k8_tmap_1(A_180,B_181))
      | ~ m1_pre_topc(B_181,A_180)
      | ~ l1_pre_topc(A_180)
      | ~ v2_pre_topc(A_180)
      | v2_struct_0(A_180) ) ),
    inference(resolution,[status(thm)],[c_22,c_1010])).

tff(c_1020,plain,(
    ! [A_182,B_183] :
      ( k6_tmap_1(A_182,u1_struct_0(B_183)) = k8_tmap_1(A_182,B_183)
      | ~ l1_pre_topc(k8_tmap_1(A_182,B_183))
      | ~ m1_pre_topc(B_183,A_182)
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(resolution,[status(thm)],[c_24,c_1015])).

tff(c_1025,plain,(
    ! [A_184,B_185] :
      ( k6_tmap_1(A_184,u1_struct_0(B_185)) = k8_tmap_1(A_184,B_185)
      | ~ m1_pre_topc(B_185,A_184)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(resolution,[status(thm)],[c_20,c_1020])).

tff(c_203,plain,(
    ! [A_89,B_90] :
      ( u1_struct_0(k6_tmap_1(A_89,B_90)) = u1_struct_0(A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_214,plain,(
    ! [A_43,B_45] :
      ( u1_struct_0(k6_tmap_1(A_43,u1_struct_0(B_45))) = u1_struct_0(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43)
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_38,c_203])).

tff(c_1331,plain,(
    ! [A_191,B_192] :
      ( u1_struct_0(k8_tmap_1(A_191,B_192)) = u1_struct_0(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191)
      | ~ m1_pre_topc(B_192,A_191)
      | ~ l1_pre_topc(A_191)
      | ~ m1_pre_topc(B_192,A_191)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1025,c_214])).

tff(c_5042,plain,(
    ! [B_357,A_358,B_359] :
      ( m1_subset_1(u1_struct_0(B_357),k1_zfmisc_1(u1_struct_0(A_358)))
      | ~ m1_pre_topc(B_357,k8_tmap_1(A_358,B_359))
      | ~ l1_pre_topc(k8_tmap_1(A_358,B_359))
      | ~ v2_pre_topc(A_358)
      | v2_struct_0(A_358)
      | ~ m1_pre_topc(B_359,A_358)
      | ~ l1_pre_topc(A_358)
      | ~ m1_pre_topc(B_359,A_358)
      | ~ l1_pre_topc(A_358)
      | ~ v2_pre_topc(A_358)
      | v2_struct_0(A_358) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1331,c_38])).

tff(c_5044,plain,
    ( m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_5042])).

tff(c_5047,plain,
    ( m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_5044])).

tff(c_5048,plain,
    ( m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5047])).

tff(c_5049,plain,(
    ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5048])).

tff(c_5052,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_5049])).

tff(c_5055,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_5052])).

tff(c_5057,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5055])).

tff(c_5059,plain,(
    l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5048])).

tff(c_42,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1124,plain,(
    ! [A_184] :
      ( k6_tmap_1(A_184,u1_struct_0('#skF_4')) = k8_tmap_1(A_184,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_184)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1025])).

tff(c_5058,plain,(
    m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_5048])).

tff(c_16,plain,(
    ! [A_26,B_27] :
      ( v2_pre_topc(k6_tmap_1(A_26,B_27))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_5073,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2',u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_5058,c_16])).

tff(c_5101,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_5073])).

tff(c_5102,plain,(
    v2_pre_topc(k6_tmap_1('#skF_2',u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5101])).

tff(c_5141,plain,
    ( v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1124,c_5102])).

tff(c_5149,plain,
    ( v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_5141])).

tff(c_5150,plain,(
    v2_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5149])).

tff(c_1127,plain,(
    ! [A_186] :
      ( k6_tmap_1(A_186,u1_struct_0('#skF_4')) = k8_tmap_1(A_186,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_186)
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1025])).

tff(c_61,plain,(
    ! [B_50,A_51] :
      ( m1_subset_1(u1_struct_0(B_50),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_pre_topc(B_50,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_64,plain,(
    ! [A_51] :
      ( m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_pre_topc('#skF_3',A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_61])).

tff(c_356,plain,(
    ! [A_94,B_95] :
      ( u1_pre_topc(k6_tmap_1(A_94,B_95)) = k5_tmap_1(A_94,B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_372,plain,(
    ! [A_51] :
      ( u1_pre_topc(k6_tmap_1(A_51,u1_struct_0('#skF_4'))) = k5_tmap_1(A_51,u1_struct_0('#skF_4'))
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51)
      | ~ m1_pre_topc('#skF_3',A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_64,c_356])).

tff(c_1174,plain,(
    ! [A_186] :
      ( k5_tmap_1(A_186,u1_struct_0('#skF_4')) = u1_pre_topc(k8_tmap_1(A_186,'#skF_3'))
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186)
      | ~ m1_pre_topc('#skF_3',A_186)
      | ~ l1_pre_topc(A_186)
      | ~ m1_pre_topc('#skF_3',A_186)
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1127,c_372])).

tff(c_26,plain,(
    ! [B_32,A_30] :
      ( r2_hidden(B_32,k5_tmap_1(A_30,B_32))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5067,plain,
    ( r2_hidden(u1_struct_0('#skF_4'),k5_tmap_1('#skF_2',u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_5058,c_26])).

tff(c_5093,plain,
    ( r2_hidden(u1_struct_0('#skF_4'),k5_tmap_1('#skF_2',u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_5067])).

tff(c_5094,plain,(
    r2_hidden(u1_struct_0('#skF_4'),k5_tmap_1('#skF_2',u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5093])).

tff(c_5260,plain,
    ( r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')))
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1174,c_5094])).

tff(c_5271,plain,
    ( r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_3')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_50,c_46,c_52,c_5260])).

tff(c_5272,plain,(
    r2_hidden(u1_struct_0('#skF_4'),u1_pre_topc(k8_tmap_1('#skF_2','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_5271])).

tff(c_76,plain,(
    ! [B_59,A_60] :
      ( v3_pre_topc(B_59,A_60)
      | ~ r2_hidden(B_59,u1_pre_topc(A_60))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_87,plain,(
    ! [B_45,A_43] :
      ( v3_pre_topc(u1_struct_0(B_45),A_43)
      | ~ r2_hidden(u1_struct_0(B_45),u1_pre_topc(A_43))
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_38,c_76])).

tff(c_6253,plain,
    ( v3_pre_topc(u1_struct_0('#skF_4'),k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_5272,c_87])).

tff(c_6274,plain,(
    v3_pre_topc(u1_struct_0('#skF_4'),k8_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5059,c_44,c_6253])).

tff(c_444,plain,(
    ! [B_101,A_102] :
      ( v1_tsep_1(B_101,A_102)
      | ~ v3_pre_topc(u1_struct_0(B_101),A_102)
      | ~ m1_subset_1(u1_struct_0(B_101),k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ m1_pre_topc(B_101,A_102)
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_470,plain,(
    ! [B_45,A_43] :
      ( v1_tsep_1(B_45,A_43)
      | ~ v3_pre_topc(u1_struct_0(B_45),A_43)
      | ~ v2_pre_topc(A_43)
      | ~ m1_pre_topc(B_45,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_38,c_444])).

tff(c_6280,plain,
    ( v1_tsep_1('#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k8_tmap_1('#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_4',k8_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k8_tmap_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_6274,c_470])).

tff(c_6286,plain,(
    v1_tsep_1('#skF_4',k8_tmap_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5059,c_44,c_5150,c_6280])).

tff(c_6288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_6286])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:55:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.24/2.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.24/2.97  
% 8.24/2.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.24/2.98  %$ v3_pre_topc > v1_tsep_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k8_tmap_1 > k6_tmap_1 > k5_tmap_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 8.24/2.98  
% 8.24/2.98  %Foreground sorts:
% 8.24/2.98  
% 8.24/2.98  
% 8.24/2.98  %Background operators:
% 8.24/2.98  
% 8.24/2.98  
% 8.24/2.98  %Foreground operators:
% 8.24/2.98  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.24/2.98  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.24/2.98  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 8.24/2.98  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 8.24/2.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.24/2.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.24/2.98  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.24/2.98  tff(k8_tmap_1, type, k8_tmap_1: ($i * $i) > $i).
% 8.24/2.98  tff('#skF_2', type, '#skF_2': $i).
% 8.24/2.98  tff('#skF_3', type, '#skF_3': $i).
% 8.24/2.98  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.24/2.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.24/2.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.24/2.98  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 8.24/2.98  tff('#skF_4', type, '#skF_4': $i).
% 8.24/2.98  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 8.24/2.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.24/2.98  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.24/2.98  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.24/2.98  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 8.24/2.98  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.24/2.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.24/2.98  
% 8.24/2.99  tff(f_164, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_pre_topc(C, k8_tmap_1(A, B)) => ((u1_struct_0(C) = u1_struct_0(B)) => (v1_tsep_1(C, k8_tmap_1(A, B)) & m1_pre_topc(C, k8_tmap_1(A, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_tmap_1)).
% 8.24/2.99  tff(f_90, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_pre_topc(B, A)) => ((v1_pre_topc(k8_tmap_1(A, B)) & v2_pre_topc(k8_tmap_1(A, B))) & l1_pre_topc(k8_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_tmap_1)).
% 8.24/2.99  tff(f_141, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 8.24/2.99  tff(f_60, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (((v1_pre_topc(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => ((C = k8_tmap_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((D = u1_struct_0(B)) => (C = k6_tmap_1(A, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_tmap_1)).
% 8.24/2.99  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 8.24/2.99  tff(f_75, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 8.24/2.99  tff(f_102, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r2_hidden(B, k5_tmap_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_tmap_1)).
% 8.24/2.99  tff(f_34, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 8.24/2.99  tff(f_134, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 8.24/2.99  tff(c_44, plain, (m1_pre_topc('#skF_4', k8_tmap_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 8.24/2.99  tff(c_40, plain, (~m1_pre_topc('#skF_4', k8_tmap_1('#skF_2', '#skF_3')) | ~v1_tsep_1('#skF_4', k8_tmap_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 8.24/2.99  tff(c_56, plain, (~v1_tsep_1('#skF_4', k8_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40])).
% 8.24/2.99  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 8.24/2.99  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 8.24/2.99  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 8.24/2.99  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_164])).
% 8.24/2.99  tff(c_20, plain, (![A_28, B_29]: (l1_pre_topc(k8_tmap_1(A_28, B_29)) | ~m1_pre_topc(B_29, A_28) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.24/2.99  tff(c_24, plain, (![A_28, B_29]: (v1_pre_topc(k8_tmap_1(A_28, B_29)) | ~m1_pre_topc(B_29, A_28) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.24/2.99  tff(c_22, plain, (![A_28, B_29]: (v2_pre_topc(k8_tmap_1(A_28, B_29)) | ~m1_pre_topc(B_29, A_28) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28) | v2_struct_0(A_28))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.24/2.99  tff(c_38, plain, (![B_45, A_43]: (m1_subset_1(u1_struct_0(B_45), k1_zfmisc_1(u1_struct_0(A_43))) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.24/2.99  tff(c_770, plain, (![A_163, B_164]: (k6_tmap_1(A_163, u1_struct_0(B_164))=k8_tmap_1(A_163, B_164) | ~m1_subset_1(u1_struct_0(B_164), k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_pre_topc(k8_tmap_1(A_163, B_164)) | ~v2_pre_topc(k8_tmap_1(A_163, B_164)) | ~v1_pre_topc(k8_tmap_1(A_163, B_164)) | ~m1_pre_topc(B_164, A_163) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_60])).
% 8.24/2.99  tff(c_1010, plain, (![A_178, B_179]: (k6_tmap_1(A_178, u1_struct_0(B_179))=k8_tmap_1(A_178, B_179) | ~l1_pre_topc(k8_tmap_1(A_178, B_179)) | ~v2_pre_topc(k8_tmap_1(A_178, B_179)) | ~v1_pre_topc(k8_tmap_1(A_178, B_179)) | ~v2_pre_topc(A_178) | v2_struct_0(A_178) | ~m1_pre_topc(B_179, A_178) | ~l1_pre_topc(A_178))), inference(resolution, [status(thm)], [c_38, c_770])).
% 8.24/2.99  tff(c_1015, plain, (![A_180, B_181]: (k6_tmap_1(A_180, u1_struct_0(B_181))=k8_tmap_1(A_180, B_181) | ~l1_pre_topc(k8_tmap_1(A_180, B_181)) | ~v1_pre_topc(k8_tmap_1(A_180, B_181)) | ~m1_pre_topc(B_181, A_180) | ~l1_pre_topc(A_180) | ~v2_pre_topc(A_180) | v2_struct_0(A_180))), inference(resolution, [status(thm)], [c_22, c_1010])).
% 8.24/2.99  tff(c_1020, plain, (![A_182, B_183]: (k6_tmap_1(A_182, u1_struct_0(B_183))=k8_tmap_1(A_182, B_183) | ~l1_pre_topc(k8_tmap_1(A_182, B_183)) | ~m1_pre_topc(B_183, A_182) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182))), inference(resolution, [status(thm)], [c_24, c_1015])).
% 8.24/2.99  tff(c_1025, plain, (![A_184, B_185]: (k6_tmap_1(A_184, u1_struct_0(B_185))=k8_tmap_1(A_184, B_185) | ~m1_pre_topc(B_185, A_184) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(resolution, [status(thm)], [c_20, c_1020])).
% 8.24/2.99  tff(c_203, plain, (![A_89, B_90]: (u1_struct_0(k6_tmap_1(A_89, B_90))=u1_struct_0(A_89) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.24/2.99  tff(c_214, plain, (![A_43, B_45]: (u1_struct_0(k6_tmap_1(A_43, u1_struct_0(B_45)))=u1_struct_0(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_38, c_203])).
% 8.24/2.99  tff(c_1331, plain, (![A_191, B_192]: (u1_struct_0(k8_tmap_1(A_191, B_192))=u1_struct_0(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191) | ~m1_pre_topc(B_192, A_191) | ~l1_pre_topc(A_191) | ~m1_pre_topc(B_192, A_191) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(superposition, [status(thm), theory('equality')], [c_1025, c_214])).
% 8.24/2.99  tff(c_5042, plain, (![B_357, A_358, B_359]: (m1_subset_1(u1_struct_0(B_357), k1_zfmisc_1(u1_struct_0(A_358))) | ~m1_pre_topc(B_357, k8_tmap_1(A_358, B_359)) | ~l1_pre_topc(k8_tmap_1(A_358, B_359)) | ~v2_pre_topc(A_358) | v2_struct_0(A_358) | ~m1_pre_topc(B_359, A_358) | ~l1_pre_topc(A_358) | ~m1_pre_topc(B_359, A_358) | ~l1_pre_topc(A_358) | ~v2_pre_topc(A_358) | v2_struct_0(A_358))), inference(superposition, [status(thm), theory('equality')], [c_1331, c_38])).
% 8.24/2.99  tff(c_5044, plain, (m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_5042])).
% 8.24/2.99  tff(c_5047, plain, (m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_5044])).
% 8.24/2.99  tff(c_5048, plain, (m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_5047])).
% 8.24/2.99  tff(c_5049, plain, (~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_5048])).
% 8.24/2.99  tff(c_5052, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_20, c_5049])).
% 8.24/2.99  tff(c_5055, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_5052])).
% 8.24/2.99  tff(c_5057, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_5055])).
% 8.24/2.99  tff(c_5059, plain, (l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_5048])).
% 8.24/2.99  tff(c_42, plain, (u1_struct_0('#skF_3')=u1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 8.24/2.99  tff(c_1124, plain, (![A_184]: (k6_tmap_1(A_184, u1_struct_0('#skF_4'))=k8_tmap_1(A_184, '#skF_3') | ~m1_pre_topc('#skF_3', A_184) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1025])).
% 8.24/2.99  tff(c_5058, plain, (m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_5048])).
% 8.24/2.99  tff(c_16, plain, (![A_26, B_27]: (v2_pre_topc(k6_tmap_1(A_26, B_27)) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.24/2.99  tff(c_5073, plain, (v2_pre_topc(k6_tmap_1('#skF_2', u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_5058, c_16])).
% 8.24/2.99  tff(c_5101, plain, (v2_pre_topc(k6_tmap_1('#skF_2', u1_struct_0('#skF_4'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_5073])).
% 8.24/2.99  tff(c_5102, plain, (v2_pre_topc(k6_tmap_1('#skF_2', u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_5101])).
% 8.24/2.99  tff(c_5141, plain, (v2_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1124, c_5102])).
% 8.24/2.99  tff(c_5149, plain, (v2_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_5141])).
% 8.24/2.99  tff(c_5150, plain, (v2_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_5149])).
% 8.24/2.99  tff(c_1127, plain, (![A_186]: (k6_tmap_1(A_186, u1_struct_0('#skF_4'))=k8_tmap_1(A_186, '#skF_3') | ~m1_pre_topc('#skF_3', A_186) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1025])).
% 8.24/2.99  tff(c_61, plain, (![B_50, A_51]: (m1_subset_1(u1_struct_0(B_50), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_pre_topc(B_50, A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_141])).
% 8.24/2.99  tff(c_64, plain, (![A_51]: (m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_pre_topc('#skF_3', A_51) | ~l1_pre_topc(A_51))), inference(superposition, [status(thm), theory('equality')], [c_42, c_61])).
% 8.24/2.99  tff(c_356, plain, (![A_94, B_95]: (u1_pre_topc(k6_tmap_1(A_94, B_95))=k5_tmap_1(A_94, B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.24/2.99  tff(c_372, plain, (![A_51]: (u1_pre_topc(k6_tmap_1(A_51, u1_struct_0('#skF_4')))=k5_tmap_1(A_51, u1_struct_0('#skF_4')) | ~v2_pre_topc(A_51) | v2_struct_0(A_51) | ~m1_pre_topc('#skF_3', A_51) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_64, c_356])).
% 8.24/2.99  tff(c_1174, plain, (![A_186]: (k5_tmap_1(A_186, u1_struct_0('#skF_4'))=u1_pre_topc(k8_tmap_1(A_186, '#skF_3')) | ~v2_pre_topc(A_186) | v2_struct_0(A_186) | ~m1_pre_topc('#skF_3', A_186) | ~l1_pre_topc(A_186) | ~m1_pre_topc('#skF_3', A_186) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(superposition, [status(thm), theory('equality')], [c_1127, c_372])).
% 8.24/2.99  tff(c_26, plain, (![B_32, A_30]: (r2_hidden(B_32, k5_tmap_1(A_30, B_32)) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.24/2.99  tff(c_5067, plain, (r2_hidden(u1_struct_0('#skF_4'), k5_tmap_1('#skF_2', u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_5058, c_26])).
% 8.24/2.99  tff(c_5093, plain, (r2_hidden(u1_struct_0('#skF_4'), k5_tmap_1('#skF_2', u1_struct_0('#skF_4'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_5067])).
% 8.24/2.99  tff(c_5094, plain, (r2_hidden(u1_struct_0('#skF_4'), k5_tmap_1('#skF_2', u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_54, c_5093])).
% 8.24/2.99  tff(c_5260, plain, (r2_hidden(u1_struct_0('#skF_4'), u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))) | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1174, c_5094])).
% 8.24/2.99  tff(c_5271, plain, (r2_hidden(u1_struct_0('#skF_4'), u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_50, c_46, c_52, c_5260])).
% 8.24/2.99  tff(c_5272, plain, (r2_hidden(u1_struct_0('#skF_4'), u1_pre_topc(k8_tmap_1('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_54, c_5271])).
% 8.24/2.99  tff(c_76, plain, (![B_59, A_60]: (v3_pre_topc(B_59, A_60) | ~r2_hidden(B_59, u1_pre_topc(A_60)) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.24/2.99  tff(c_87, plain, (![B_45, A_43]: (v3_pre_topc(u1_struct_0(B_45), A_43) | ~r2_hidden(u1_struct_0(B_45), u1_pre_topc(A_43)) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_38, c_76])).
% 8.24/2.99  tff(c_6253, plain, (v3_pre_topc(u1_struct_0('#skF_4'), k8_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_4', k8_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_5272, c_87])).
% 8.24/2.99  tff(c_6274, plain, (v3_pre_topc(u1_struct_0('#skF_4'), k8_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5059, c_44, c_6253])).
% 8.24/2.99  tff(c_444, plain, (![B_101, A_102]: (v1_tsep_1(B_101, A_102) | ~v3_pre_topc(u1_struct_0(B_101), A_102) | ~m1_subset_1(u1_struct_0(B_101), k1_zfmisc_1(u1_struct_0(A_102))) | ~m1_pre_topc(B_101, A_102) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_134])).
% 8.24/2.99  tff(c_470, plain, (![B_45, A_43]: (v1_tsep_1(B_45, A_43) | ~v3_pre_topc(u1_struct_0(B_45), A_43) | ~v2_pre_topc(A_43) | ~m1_pre_topc(B_45, A_43) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_38, c_444])).
% 8.24/2.99  tff(c_6280, plain, (v1_tsep_1('#skF_4', k8_tmap_1('#skF_2', '#skF_3')) | ~v2_pre_topc(k8_tmap_1('#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_4', k8_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k8_tmap_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_6274, c_470])).
% 8.24/2.99  tff(c_6286, plain, (v1_tsep_1('#skF_4', k8_tmap_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5059, c_44, c_5150, c_6280])).
% 8.24/2.99  tff(c_6288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_6286])).
% 8.24/2.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.24/2.99  
% 8.24/2.99  Inference rules
% 8.24/2.99  ----------------------
% 8.24/2.99  #Ref     : 0
% 8.24/2.99  #Sup     : 1761
% 8.24/2.99  #Fact    : 0
% 8.24/2.99  #Define  : 0
% 8.24/2.99  #Split   : 4
% 8.24/2.99  #Chain   : 0
% 8.24/2.99  #Close   : 0
% 8.24/2.99  
% 8.24/2.99  Ordering : KBO
% 8.24/2.99  
% 8.24/2.99  Simplification rules
% 8.24/2.99  ----------------------
% 8.24/2.99  #Subsume      : 204
% 8.24/2.99  #Demod        : 501
% 8.24/2.99  #Tautology    : 187
% 8.24/2.99  #SimpNegUnit  : 85
% 8.24/2.99  #BackRed      : 0
% 8.24/2.99  
% 8.24/2.99  #Partial instantiations: 0
% 8.24/2.99  #Strategies tried      : 1
% 8.24/2.99  
% 8.24/2.99  Timing (in seconds)
% 8.24/2.99  ----------------------
% 8.49/3.00  Preprocessing        : 0.34
% 8.49/3.00  Parsing              : 0.17
% 8.49/3.00  CNF conversion       : 0.03
% 8.49/3.00  Main loop            : 1.88
% 8.49/3.00  Inferencing          : 0.50
% 8.49/3.00  Reduction            : 0.43
% 8.49/3.00  Demodulation         : 0.28
% 8.49/3.00  BG Simplification    : 0.08
% 8.49/3.00  Subsumption          : 0.78
% 8.49/3.00  Abstraction          : 0.07
% 8.49/3.00  MUC search           : 0.00
% 8.49/3.00  Cooper               : 0.00
% 8.49/3.00  Total                : 2.26
% 8.49/3.00  Index Insertion      : 0.00
% 8.49/3.00  Index Deletion       : 0.00
% 8.49/3.00  Index Matching       : 0.00
% 8.49/3.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
