%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:19 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   82 (1284 expanded)
%              Number of leaves         :   28 ( 446 expanded)
%              Depth                    :   21
%              Number of atoms          :  163 (4236 expanded)
%              Number of equality atoms :   32 ( 645 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v4_tex_2,type,(
    v4_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ~ ( v3_tex_2(B,A)
                & ! [C] :
                    ( ( ~ v2_struct_0(C)
                      & v1_pre_topc(C)
                      & m1_pre_topc(C,A) )
                   => ~ ( v4_tex_2(C,A)
                        & B = u1_struct_0(C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tex_2)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v4_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v3_tex_2(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tex_2)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_pre_topc(A,B)
              <=> k2_struct_0(C) = B ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_struct_0)).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_12,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    ! [A_32] :
      ( u1_struct_0(A_32) = k2_struct_0(A_32)
      | ~ l1_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45,plain,(
    ! [A_33] :
      ( u1_struct_0(A_33) = k2_struct_0(A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(resolution,[status(thm)],[c_12,c_40])).

tff(c_49,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_45])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_51,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_30])).

tff(c_64,plain,(
    ! [A_40,B_41] :
      ( m1_pre_topc(k1_pre_topc(A_40,B_41),A_40)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_66,plain,(
    ! [B_41] :
      ( m1_pre_topc(k1_pre_topc('#skF_2',B_41),'#skF_2')
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_64])).

tff(c_74,plain,(
    ! [B_43] :
      ( m1_pre_topc(k1_pre_topc('#skF_2',B_43),'#skF_2')
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_66])).

tff(c_78,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_51,c_74])).

tff(c_14,plain,(
    ! [B_14,A_12] :
      ( l1_pre_topc(B_14)
      | ~ m1_pre_topc(B_14,A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_81,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_14])).

tff(c_84,plain,(
    l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_81])).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_44,plain,(
    ! [A_11] :
      ( u1_struct_0(A_11) = k2_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_40])).

tff(c_88,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_84,c_44])).

tff(c_58,plain,(
    ! [A_38,B_39] :
      ( v1_pre_topc(k1_pre_topc(A_38,B_39))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_61,plain,(
    ! [B_39] :
      ( v1_pre_topc(k1_pre_topc('#skF_2',B_39))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_58])).

tff(c_69,plain,(
    ! [B_42] :
      ( v1_pre_topc(k1_pre_topc('#skF_2',B_42))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_61])).

tff(c_73,plain,(
    v1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_51,c_69])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_103,plain,(
    ! [B_45,A_46] :
      ( u1_struct_0(B_45) = '#skF_1'(A_46,B_45)
      | v4_tex_2(B_45,A_46)
      | ~ m1_pre_topc(B_45,A_46)
      | ~ l1_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    ! [C_30] :
      ( u1_struct_0(C_30) != '#skF_3'
      | ~ v4_tex_2(C_30,'#skF_2')
      | ~ m1_pre_topc(C_30,'#skF_2')
      | ~ v1_pre_topc(C_30)
      | v2_struct_0(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_107,plain,(
    ! [B_45] :
      ( u1_struct_0(B_45) != '#skF_3'
      | ~ v1_pre_topc(B_45)
      | v2_struct_0(B_45)
      | u1_struct_0(B_45) = '#skF_1'('#skF_2',B_45)
      | ~ m1_pre_topc(B_45,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_103,c_26])).

tff(c_110,plain,(
    ! [B_45] :
      ( u1_struct_0(B_45) != '#skF_3'
      | ~ v1_pre_topc(B_45)
      | v2_struct_0(B_45)
      | u1_struct_0(B_45) = '#skF_1'('#skF_2',B_45)
      | ~ m1_pre_topc(B_45,'#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_107])).

tff(c_149,plain,(
    ! [B_54] :
      ( u1_struct_0(B_54) != '#skF_3'
      | ~ v1_pre_topc(B_54)
      | v2_struct_0(B_54)
      | u1_struct_0(B_54) = '#skF_1'('#skF_2',B_54)
      | ~ m1_pre_topc(B_54,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_110])).

tff(c_155,plain,
    ( u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) != '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | v2_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_78,c_149])).

tff(c_159,plain,
    ( k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) != '#skF_3'
    | v2_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_73,c_88,c_155])).

tff(c_217,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_259,plain,(
    ! [A_71,B_72] :
      ( k2_struct_0(k1_pre_topc(A_71,B_72)) = B_72
      | ~ m1_pre_topc(k1_pre_topc(A_71,B_72),A_71)
      | ~ v1_pre_topc(k1_pre_topc(A_71,B_72))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_265,plain,
    ( k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_259])).

tff(c_272,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_51,c_49,c_73,c_265])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_272])).

tff(c_276,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_16,plain,(
    ! [A_15] :
      ( v1_xboole_0(k2_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | ~ v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_289,plain,
    ( v1_xboole_0('#skF_3')
    | ~ l1_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_16])).

tff(c_296,plain,
    ( ~ l1_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_289])).

tff(c_321,plain,(
    ~ v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_279,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_88])).

tff(c_28,plain,(
    v3_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_275,plain,
    ( k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'))
    | v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_324,plain,
    ( '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_275])).

tff(c_325,plain,(
    '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_321,c_324])).

tff(c_20,plain,(
    ! [A_16,B_22] :
      ( ~ v3_tex_2('#skF_1'(A_16,B_22),A_16)
      | v4_tex_2(B_22,A_16)
      | ~ m1_pre_topc(B_22,A_16)
      | ~ l1_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_359,plain,
    ( ~ v3_tex_2('#skF_3','#skF_2')
    | v4_tex_2(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_20])).

tff(c_388,plain,
    ( v4_tex_2(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_78,c_28,c_359])).

tff(c_389,plain,(
    v4_tex_2(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_388])).

tff(c_393,plain,
    ( u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) != '#skF_3'
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_389,c_26])).

tff(c_396,plain,(
    v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_78,c_279,c_393])).

tff(c_398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_321,c_396])).

tff(c_399,plain,(
    ~ l1_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_429,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_399])).

tff(c_433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_429])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.36  
% 2.49/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.36  %$ v4_tex_2 > v3_tex_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.66/1.36  
% 2.66/1.36  %Foreground sorts:
% 2.66/1.36  
% 2.66/1.36  
% 2.66/1.36  %Background operators:
% 2.66/1.36  
% 2.66/1.36  
% 2.66/1.36  %Foreground operators:
% 2.66/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.66/1.36  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 2.66/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.36  tff(v4_tex_2, type, v4_tex_2: ($i * $i) > $o).
% 2.66/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.66/1.36  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 2.66/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.36  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.66/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.66/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.36  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.66/1.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.66/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.66/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.66/1.36  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.66/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.66/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.36  
% 2.66/1.38  tff(f_115, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v3_tex_2(B, A) & (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ~(v4_tex_2(C, A) & (B = u1_struct_0(C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_tex_2)).
% 2.66/1.38  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.66/1.38  tff(f_43, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.66/1.38  tff(f_51, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 2.66/1.38  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.66/1.38  tff(f_85, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (v4_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v3_tex_2(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_tex_2)).
% 2.66/1.38  tff(f_39, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_pre_topc)).
% 2.66/1.38  tff(f_68, axiom, (![A]: ((v2_struct_0(A) & l1_struct_0(A)) => v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_struct_0)).
% 2.66/1.38  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.66/1.38  tff(c_12, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.66/1.38  tff(c_40, plain, (![A_32]: (u1_struct_0(A_32)=k2_struct_0(A_32) | ~l1_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.66/1.38  tff(c_45, plain, (![A_33]: (u1_struct_0(A_33)=k2_struct_0(A_33) | ~l1_pre_topc(A_33))), inference(resolution, [status(thm)], [c_12, c_40])).
% 2.66/1.38  tff(c_49, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_45])).
% 2.66/1.38  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.66/1.38  tff(c_51, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_30])).
% 2.66/1.38  tff(c_64, plain, (![A_40, B_41]: (m1_pre_topc(k1_pre_topc(A_40, B_41), A_40) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.66/1.38  tff(c_66, plain, (![B_41]: (m1_pre_topc(k1_pre_topc('#skF_2', B_41), '#skF_2') | ~m1_subset_1(B_41, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_49, c_64])).
% 2.66/1.38  tff(c_74, plain, (![B_43]: (m1_pre_topc(k1_pre_topc('#skF_2', B_43), '#skF_2') | ~m1_subset_1(B_43, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_66])).
% 2.66/1.38  tff(c_78, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_51, c_74])).
% 2.66/1.38  tff(c_14, plain, (![B_14, A_12]: (l1_pre_topc(B_14) | ~m1_pre_topc(B_14, A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.66/1.38  tff(c_81, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_78, c_14])).
% 2.66/1.38  tff(c_84, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_81])).
% 2.66/1.38  tff(c_32, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.66/1.38  tff(c_44, plain, (![A_11]: (u1_struct_0(A_11)=k2_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(resolution, [status(thm)], [c_12, c_40])).
% 2.66/1.38  tff(c_88, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))=k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_84, c_44])).
% 2.66/1.38  tff(c_58, plain, (![A_38, B_39]: (v1_pre_topc(k1_pre_topc(A_38, B_39)) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_struct_0(A_38))) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.66/1.38  tff(c_61, plain, (![B_39]: (v1_pre_topc(k1_pre_topc('#skF_2', B_39)) | ~m1_subset_1(B_39, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_49, c_58])).
% 2.66/1.38  tff(c_69, plain, (![B_42]: (v1_pre_topc(k1_pre_topc('#skF_2', B_42)) | ~m1_subset_1(B_42, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_61])).
% 2.66/1.38  tff(c_73, plain, (v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_51, c_69])).
% 2.66/1.38  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.66/1.38  tff(c_103, plain, (![B_45, A_46]: (u1_struct_0(B_45)='#skF_1'(A_46, B_45) | v4_tex_2(B_45, A_46) | ~m1_pre_topc(B_45, A_46) | ~l1_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.66/1.38  tff(c_26, plain, (![C_30]: (u1_struct_0(C_30)!='#skF_3' | ~v4_tex_2(C_30, '#skF_2') | ~m1_pre_topc(C_30, '#skF_2') | ~v1_pre_topc(C_30) | v2_struct_0(C_30))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.66/1.38  tff(c_107, plain, (![B_45]: (u1_struct_0(B_45)!='#skF_3' | ~v1_pre_topc(B_45) | v2_struct_0(B_45) | u1_struct_0(B_45)='#skF_1'('#skF_2', B_45) | ~m1_pre_topc(B_45, '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_103, c_26])).
% 2.66/1.38  tff(c_110, plain, (![B_45]: (u1_struct_0(B_45)!='#skF_3' | ~v1_pre_topc(B_45) | v2_struct_0(B_45) | u1_struct_0(B_45)='#skF_1'('#skF_2', B_45) | ~m1_pre_topc(B_45, '#skF_2') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_107])).
% 2.66/1.38  tff(c_149, plain, (![B_54]: (u1_struct_0(B_54)!='#skF_3' | ~v1_pre_topc(B_54) | v2_struct_0(B_54) | u1_struct_0(B_54)='#skF_1'('#skF_2', B_54) | ~m1_pre_topc(B_54, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_38, c_110])).
% 2.66/1.38  tff(c_155, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))!='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | v2_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_78, c_149])).
% 2.66/1.38  tff(c_159, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))!='#skF_3' | v2_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_73, c_88, c_155])).
% 2.66/1.38  tff(c_217, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_159])).
% 2.66/1.38  tff(c_259, plain, (![A_71, B_72]: (k2_struct_0(k1_pre_topc(A_71, B_72))=B_72 | ~m1_pre_topc(k1_pre_topc(A_71, B_72), A_71) | ~v1_pre_topc(k1_pre_topc(A_71, B_72)) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.66/1.38  tff(c_265, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_78, c_259])).
% 2.66/1.38  tff(c_272, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_51, c_49, c_73, c_265])).
% 2.66/1.38  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_217, c_272])).
% 2.66/1.38  tff(c_276, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(splitRight, [status(thm)], [c_159])).
% 2.66/1.38  tff(c_16, plain, (![A_15]: (v1_xboole_0(k2_struct_0(A_15)) | ~l1_struct_0(A_15) | ~v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.66/1.38  tff(c_289, plain, (v1_xboole_0('#skF_3') | ~l1_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_276, c_16])).
% 2.66/1.38  tff(c_296, plain, (~l1_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_32, c_289])).
% 2.66/1.38  tff(c_321, plain, (~v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_296])).
% 2.66/1.38  tff(c_279, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_276, c_88])).
% 2.66/1.38  tff(c_28, plain, (v3_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.66/1.38  tff(c_275, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3')) | v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_159])).
% 2.66/1.38  tff(c_324, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'))='#skF_3' | v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_275])).
% 2.66/1.38  tff(c_325, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_321, c_324])).
% 2.66/1.38  tff(c_20, plain, (![A_16, B_22]: (~v3_tex_2('#skF_1'(A_16, B_22), A_16) | v4_tex_2(B_22, A_16) | ~m1_pre_topc(B_22, A_16) | ~l1_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.66/1.38  tff(c_359, plain, (~v3_tex_2('#skF_3', '#skF_2') | v4_tex_2(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_325, c_20])).
% 2.66/1.38  tff(c_388, plain, (v4_tex_2(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_78, c_28, c_359])).
% 2.66/1.38  tff(c_389, plain, (v4_tex_2(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_38, c_388])).
% 2.66/1.38  tff(c_393, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))!='#skF_3' | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_389, c_26])).
% 2.66/1.38  tff(c_396, plain, (v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_78, c_279, c_393])).
% 2.66/1.38  tff(c_398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_321, c_396])).
% 2.66/1.38  tff(c_399, plain, (~l1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_296])).
% 2.66/1.38  tff(c_429, plain, (~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_399])).
% 2.66/1.38  tff(c_433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_429])).
% 2.66/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.66/1.38  
% 2.66/1.38  Inference rules
% 2.66/1.38  ----------------------
% 2.66/1.38  #Ref     : 0
% 2.66/1.38  #Sup     : 80
% 2.66/1.38  #Fact    : 0
% 2.66/1.38  #Define  : 0
% 2.66/1.38  #Split   : 3
% 2.66/1.38  #Chain   : 0
% 2.66/1.38  #Close   : 0
% 2.66/1.38  
% 2.66/1.38  Ordering : KBO
% 2.66/1.38  
% 2.66/1.38  Simplification rules
% 2.66/1.38  ----------------------
% 2.66/1.38  #Subsume      : 1
% 2.66/1.38  #Demod        : 88
% 2.66/1.38  #Tautology    : 23
% 2.66/1.38  #SimpNegUnit  : 15
% 2.66/1.38  #BackRed      : 4
% 2.66/1.38  
% 2.66/1.38  #Partial instantiations: 0
% 2.66/1.38  #Strategies tried      : 1
% 2.66/1.38  
% 2.66/1.38  Timing (in seconds)
% 2.66/1.38  ----------------------
% 2.66/1.38  Preprocessing        : 0.32
% 2.66/1.38  Parsing              : 0.17
% 2.66/1.38  CNF conversion       : 0.02
% 2.66/1.38  Main loop            : 0.28
% 2.66/1.38  Inferencing          : 0.10
% 2.66/1.38  Reduction            : 0.09
% 2.66/1.38  Demodulation         : 0.06
% 2.66/1.38  BG Simplification    : 0.02
% 2.66/1.38  Subsumption          : 0.06
% 2.66/1.39  Abstraction          : 0.02
% 2.66/1.39  MUC search           : 0.00
% 2.66/1.39  Cooper               : 0.00
% 2.66/1.39  Total                : 0.63
% 2.66/1.39  Index Insertion      : 0.00
% 2.66/1.39  Index Deletion       : 0.00
% 2.66/1.39  Index Matching       : 0.00
% 2.66/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
