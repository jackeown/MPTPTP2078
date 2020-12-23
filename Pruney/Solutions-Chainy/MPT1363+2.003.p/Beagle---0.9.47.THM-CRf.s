%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:54 EST 2020

% Result     : Theorem 4.60s
% Output     : CNFRefutation 4.84s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 705 expanded)
%              Number of leaves         :   30 ( 272 expanded)
%              Depth                    :   18
%              Number of atoms          :  286 (2717 expanded)
%              Number of equality atoms :   29 ( 131 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > v1_compts_1 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_compts_1(B,A)
                    & r1_tarski(C,B)
                    & v4_pre_topc(C,A) )
                 => v2_compts_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

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

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(C,k2_struct_0(B))
               => ( v2_compts_1(C,A)
                <=> ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                     => ( D = C
                       => v2_compts_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( B = k1_xboole_0
             => ( v2_compts_1(B,A)
              <=> v1_compts_1(k1_pre_topc(A,B)) ) )
            & ( v2_pre_topc(A)
             => ( B = k1_xboole_0
                | ( v2_compts_1(B,A)
                <=> v1_compts_1(k1_pre_topc(A,B)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_compts_1)).

tff(f_130,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v1_compts_1(A)
              & v4_pre_topc(B,A) )
           => v2_compts_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_compts_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v4_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v4_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_63,plain,(
    ! [A_71,B_72] :
      ( m1_pre_topc(k1_pre_topc(A_71,B_72),A_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_67,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_63])).

tff(c_73,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_67])).

tff(c_36,plain,(
    v4_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_34,plain,(
    ~ v2_compts_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_38,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_50,plain,(
    ! [A_69,B_70] :
      ( v1_pre_topc(k1_pre_topc(A_69,B_70))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_56,plain,
    ( v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_50])).

tff(c_62,plain,(
    v1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_56])).

tff(c_1415,plain,(
    ! [A_195,B_196] :
      ( k2_struct_0(k1_pre_topc(A_195,B_196)) = B_196
      | ~ m1_pre_topc(k1_pre_topc(A_195,B_196),A_195)
      | ~ v1_pre_topc(k1_pre_topc(A_195,B_196))
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ l1_pre_topc(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1421,plain,
    ( k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_1415])).

tff(c_1428,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_62,c_1421])).

tff(c_1441,plain,(
    ! [A_197,B_198,C_199] :
      ( '#skF_1'(A_197,B_198,C_199) = C_199
      | v2_compts_1(C_199,A_197)
      | ~ r1_tarski(C_199,k2_struct_0(B_198))
      | ~ m1_subset_1(C_199,k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ m1_pre_topc(B_198,A_197)
      | ~ l1_pre_topc(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1762,plain,(
    ! [A_237,C_238] :
      ( '#skF_1'(A_237,k1_pre_topc('#skF_2','#skF_3'),C_238) = C_238
      | v2_compts_1(C_238,A_237)
      | ~ r1_tarski(C_238,'#skF_3')
      | ~ m1_subset_1(C_238,k1_zfmisc_1(u1_struct_0(A_237)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_237)
      | ~ l1_pre_topc(A_237) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1428,c_1441])).

tff(c_1774,plain,
    ( '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_4') = '#skF_4'
    | v2_compts_1('#skF_4','#skF_2')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_1762])).

tff(c_1785,plain,
    ( '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_4') = '#skF_4'
    | v2_compts_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_73,c_38,c_1774])).

tff(c_1786,plain,(
    '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1785])).

tff(c_18,plain,(
    ! [A_35,B_47,C_53] :
      ( ~ v2_compts_1('#skF_1'(A_35,B_47,C_53),B_47)
      | v2_compts_1(C_53,A_35)
      | ~ r1_tarski(C_53,k2_struct_0(B_47))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_pre_topc(B_47,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1801,plain,
    ( ~ v2_compts_1('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
    | v2_compts_1('#skF_4','#skF_2')
    | ~ r1_tarski('#skF_4',k2_struct_0(k1_pre_topc('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1786,c_18])).

tff(c_1813,plain,
    ( ~ v2_compts_1('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
    | v2_compts_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_73,c_42,c_38,c_1428,c_1801])).

tff(c_1814,plain,(
    ~ v2_compts_1('#skF_4',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1813])).

tff(c_10,plain,(
    ! [B_12,A_10] :
      ( l1_pre_topc(B_12)
      | ~ m1_pre_topc(B_12,A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_83,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_10])).

tff(c_86,plain,(
    l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_83])).

tff(c_359,plain,(
    ! [A_108,B_109] :
      ( k2_struct_0(k1_pre_topc(A_108,B_109)) = B_109
      | ~ m1_pre_topc(k1_pre_topc(A_108,B_109),A_108)
      | ~ v1_pre_topc(k1_pre_topc(A_108,B_109))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_365,plain,
    ( k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | ~ v1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_359])).

tff(c_372,plain,(
    k2_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_62,c_365])).

tff(c_448,plain,(
    ! [A_117,B_118,C_119] :
      ( '#skF_1'(A_117,B_118,C_119) = C_119
      | v2_compts_1(C_119,A_117)
      | ~ r1_tarski(C_119,k2_struct_0(B_118))
      | ~ m1_subset_1(C_119,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m1_pre_topc(B_118,A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_710,plain,(
    ! [A_147,C_148] :
      ( '#skF_1'(A_147,k1_pre_topc('#skF_2','#skF_3'),C_148) = C_148
      | v2_compts_1(C_148,A_147)
      | ~ r1_tarski(C_148,'#skF_3')
      | ~ m1_subset_1(C_148,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_147)
      | ~ l1_pre_topc(A_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_448])).

tff(c_722,plain,
    ( '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_4') = '#skF_4'
    | v2_compts_1('#skF_4','#skF_2')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_710])).

tff(c_733,plain,
    ( '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_4') = '#skF_4'
    | v2_compts_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_73,c_38,c_722])).

tff(c_734,plain,(
    '#skF_1'('#skF_2',k1_pre_topc('#skF_2','#skF_3'),'#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_733])).

tff(c_764,plain,
    ( ~ v2_compts_1('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
    | v2_compts_1('#skF_4','#skF_2')
    | ~ r1_tarski('#skF_4',k2_struct_0(k1_pre_topc('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_734,c_18])).

tff(c_771,plain,
    ( ~ v2_compts_1('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
    | v2_compts_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_73,c_42,c_38,c_372,c_764])).

tff(c_772,plain,(
    ~ v2_compts_1('#skF_4',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_771])).

tff(c_40,plain,(
    v2_compts_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_102,plain,(
    ! [C_77,A_78,B_79] :
      ( m1_subset_1(C_77,k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ m1_subset_1(C_77,k1_zfmisc_1(u1_struct_0(B_79)))
      | ~ m1_pre_topc(B_79,A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_108,plain,(
    ! [A_78] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_78)))
      | ~ m1_pre_topc('#skF_2',A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_44,c_102])).

tff(c_197,plain,(
    ! [B_96,A_97] :
      ( v2_compts_1(B_96,A_97)
      | ~ v1_compts_1(k1_pre_topc(A_97,B_96))
      | k1_xboole_0 = B_96
      | ~ v2_pre_topc(A_97)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_210,plain,(
    ! [A_78] :
      ( v2_compts_1('#skF_3',A_78)
      | ~ v1_compts_1(k1_pre_topc(A_78,'#skF_3'))
      | k1_xboole_0 = '#skF_3'
      | ~ v2_pre_topc(A_78)
      | ~ m1_pre_topc('#skF_2',A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(resolution,[status(thm)],[c_108,c_197])).

tff(c_220,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_30,plain,(
    ! [A_57] :
      ( v1_compts_1(k1_pre_topc(A_57,k1_xboole_0))
      | ~ v2_compts_1(k1_xboole_0,A_57)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_313,plain,(
    ! [A_104] :
      ( v1_compts_1(k1_pre_topc(A_104,'#skF_3'))
      | ~ v2_compts_1('#skF_3',A_104)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_220,c_220,c_30])).

tff(c_319,plain,
    ( v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_compts_1('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_313])).

tff(c_323,plain,(
    v1_compts_1(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_40,c_319])).

tff(c_22,plain,(
    ! [A_35,B_47,C_53] :
      ( m1_subset_1('#skF_1'(A_35,B_47,C_53),k1_zfmisc_1(u1_struct_0(B_47)))
      | v2_compts_1(C_53,A_35)
      | ~ r1_tarski(C_53,k2_struct_0(B_47))
      | ~ m1_subset_1(C_53,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_pre_topc(B_47,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_762,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3'))))
    | v2_compts_1('#skF_4','#skF_2')
    | ~ r1_tarski('#skF_4',k2_struct_0(k1_pre_topc('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_734,c_22])).

tff(c_768,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3'))))
    | v2_compts_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_73,c_42,c_38,c_372,c_762])).

tff(c_769,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_768])).

tff(c_32,plain,(
    ! [B_62,A_60] :
      ( v2_compts_1(B_62,A_60)
      | ~ v4_pre_topc(B_62,A_60)
      | ~ v1_compts_1(A_60)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_799,plain,
    ( v2_compts_1('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
    | ~ v4_pre_topc('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
    | ~ v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_769,c_32])).

tff(c_836,plain,
    ( v2_compts_1('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
    | ~ v4_pre_topc('#skF_4',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_323,c_799])).

tff(c_837,plain,(
    ~ v4_pre_topc('#skF_4',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_772,c_836])).

tff(c_14,plain,(
    ! [D_34,C_32,A_20] :
      ( v4_pre_topc(D_34,C_32)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(u1_struct_0(C_32)))
      | ~ v4_pre_topc(D_34,A_20)
      | ~ m1_pre_topc(C_32,A_20)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_824,plain,(
    ! [A_20] :
      ( v4_pre_topc('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
      | ~ v4_pre_topc('#skF_4',A_20)
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_20)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(resolution,[status(thm)],[c_769,c_14])).

tff(c_1231,plain,(
    ! [A_177] :
      ( ~ v4_pre_topc('#skF_4',A_177)
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_177)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177) ) ),
    inference(negUnitSimplification,[status(thm)],[c_837,c_824])).

tff(c_1243,plain,
    ( ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_1231])).

tff(c_1252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_73,c_36,c_1243])).

tff(c_1254,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1257,plain,(
    ! [A_179,B_180] :
      ( v1_compts_1(k1_pre_topc(A_179,B_180))
      | ~ v2_compts_1(B_180,A_179)
      | k1_xboole_0 = B_180
      | ~ v2_pre_topc(A_179)
      | ~ m1_subset_1(B_180,k1_zfmisc_1(u1_struct_0(A_179)))
      | ~ l1_pre_topc(A_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1269,plain,
    ( v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_compts_1('#skF_3','#skF_2')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1257])).

tff(c_1280,plain,
    ( v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_40,c_1269])).

tff(c_1281,plain,(
    v1_compts_1(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1254,c_1280])).

tff(c_1799,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3'))))
    | v2_compts_1('#skF_4','#skF_2')
    | ~ r1_tarski('#skF_4',k2_struct_0(k1_pre_topc('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1786,c_22])).

tff(c_1810,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3'))))
    | v2_compts_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_73,c_42,c_38,c_1428,c_1799])).

tff(c_1811,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2','#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1810])).

tff(c_1847,plain,
    ( v2_compts_1('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
    | ~ v4_pre_topc('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
    | ~ v1_compts_1(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1811,c_32])).

tff(c_1891,plain,
    ( v2_compts_1('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
    | ~ v4_pre_topc('#skF_4',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1281,c_1847])).

tff(c_1892,plain,(
    ~ v4_pre_topc('#skF_4',k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1814,c_1891])).

tff(c_1880,plain,(
    ! [A_20] :
      ( v4_pre_topc('#skF_4',k1_pre_topc('#skF_2','#skF_3'))
      | ~ v4_pre_topc('#skF_4',A_20)
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_20)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(resolution,[status(thm)],[c_1811,c_14])).

tff(c_2279,plain,(
    ! [A_261] :
      ( ~ v4_pre_topc('#skF_4',A_261)
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_261)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_261)))
      | ~ l1_pre_topc(A_261) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1892,c_1880])).

tff(c_2291,plain,
    ( ~ v4_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_2279])).

tff(c_2300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_73,c_36,c_2291])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.60/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.81  
% 4.60/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.82  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > v1_compts_1 > l1_pre_topc > k1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 4.60/1.82  
% 4.60/1.82  %Foreground sorts:
% 4.60/1.82  
% 4.60/1.82  
% 4.60/1.82  %Background operators:
% 4.60/1.82  
% 4.60/1.82  
% 4.60/1.82  %Foreground operators:
% 4.60/1.82  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 4.60/1.82  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 4.60/1.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.60/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.60/1.82  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.60/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.60/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.60/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.60/1.82  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.60/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.60/1.82  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.60/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.60/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.82  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.60/1.82  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.60/1.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.60/1.82  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 4.60/1.82  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.60/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.60/1.82  
% 4.84/1.84  tff(f_149, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 4.84/1.84  tff(f_47, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 4.84/1.84  tff(f_39, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((v1_pre_topc(C) & m1_pre_topc(C, A)) => ((C = k1_pre_topc(A, B)) <=> (k2_struct_0(C) = B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_pre_topc)).
% 4.84/1.84  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, k2_struct_0(B)) => (v2_compts_1(C, A) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((D = C) => v2_compts_1(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_compts_1)).
% 4.84/1.84  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.84/1.84  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 4.84/1.84  tff(f_119, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (((B = k1_xboole_0) => (v2_compts_1(B, A) <=> v1_compts_1(k1_pre_topc(A, B)))) & (v2_pre_topc(A) => ((B = k1_xboole_0) | (v2_compts_1(B, A) <=> v1_compts_1(k1_pre_topc(A, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_compts_1)).
% 4.84/1.84  tff(f_130, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v1_compts_1(A) & v4_pre_topc(B, A)) => v2_compts_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_compts_1)).
% 4.84/1.84  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v4_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v4_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tops_2)).
% 4.84/1.84  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.84/1.84  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.84/1.84  tff(c_63, plain, (![A_71, B_72]: (m1_pre_topc(k1_pre_topc(A_71, B_72), A_71) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.84/1.84  tff(c_67, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_63])).
% 4.84/1.84  tff(c_73, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_67])).
% 4.84/1.84  tff(c_36, plain, (v4_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.84/1.84  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.84/1.84  tff(c_34, plain, (~v2_compts_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.84/1.84  tff(c_38, plain, (r1_tarski('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.84/1.84  tff(c_50, plain, (![A_69, B_70]: (v1_pre_topc(k1_pre_topc(A_69, B_70)) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.84/1.84  tff(c_56, plain, (v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_50])).
% 4.84/1.84  tff(c_62, plain, (v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_56])).
% 4.84/1.84  tff(c_1415, plain, (![A_195, B_196]: (k2_struct_0(k1_pre_topc(A_195, B_196))=B_196 | ~m1_pre_topc(k1_pre_topc(A_195, B_196), A_195) | ~v1_pre_topc(k1_pre_topc(A_195, B_196)) | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0(A_195))) | ~l1_pre_topc(A_195))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.84/1.84  tff(c_1421, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_73, c_1415])).
% 4.84/1.84  tff(c_1428, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_62, c_1421])).
% 4.84/1.84  tff(c_1441, plain, (![A_197, B_198, C_199]: ('#skF_1'(A_197, B_198, C_199)=C_199 | v2_compts_1(C_199, A_197) | ~r1_tarski(C_199, k2_struct_0(B_198)) | ~m1_subset_1(C_199, k1_zfmisc_1(u1_struct_0(A_197))) | ~m1_pre_topc(B_198, A_197) | ~l1_pre_topc(A_197))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.84/1.84  tff(c_1762, plain, (![A_237, C_238]: ('#skF_1'(A_237, k1_pre_topc('#skF_2', '#skF_3'), C_238)=C_238 | v2_compts_1(C_238, A_237) | ~r1_tarski(C_238, '#skF_3') | ~m1_subset_1(C_238, k1_zfmisc_1(u1_struct_0(A_237))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), A_237) | ~l1_pre_topc(A_237))), inference(superposition, [status(thm), theory('equality')], [c_1428, c_1441])).
% 4.84/1.84  tff(c_1774, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), '#skF_4')='#skF_4' | v2_compts_1('#skF_4', '#skF_2') | ~r1_tarski('#skF_4', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_1762])).
% 4.84/1.84  tff(c_1785, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), '#skF_4')='#skF_4' | v2_compts_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_73, c_38, c_1774])).
% 4.84/1.84  tff(c_1786, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_34, c_1785])).
% 4.84/1.84  tff(c_18, plain, (![A_35, B_47, C_53]: (~v2_compts_1('#skF_1'(A_35, B_47, C_53), B_47) | v2_compts_1(C_53, A_35) | ~r1_tarski(C_53, k2_struct_0(B_47)) | ~m1_subset_1(C_53, k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_pre_topc(B_47, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.84/1.84  tff(c_1801, plain, (~v2_compts_1('#skF_4', k1_pre_topc('#skF_2', '#skF_3')) | v2_compts_1('#skF_4', '#skF_2') | ~r1_tarski('#skF_4', k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1786, c_18])).
% 4.84/1.84  tff(c_1813, plain, (~v2_compts_1('#skF_4', k1_pre_topc('#skF_2', '#skF_3')) | v2_compts_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_73, c_42, c_38, c_1428, c_1801])).
% 4.84/1.84  tff(c_1814, plain, (~v2_compts_1('#skF_4', k1_pre_topc('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_34, c_1813])).
% 4.84/1.84  tff(c_10, plain, (![B_12, A_10]: (l1_pre_topc(B_12) | ~m1_pre_topc(B_12, A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.84/1.84  tff(c_83, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_73, c_10])).
% 4.84/1.84  tff(c_86, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_83])).
% 4.84/1.84  tff(c_359, plain, (![A_108, B_109]: (k2_struct_0(k1_pre_topc(A_108, B_109))=B_109 | ~m1_pre_topc(k1_pre_topc(A_108, B_109), A_108) | ~v1_pre_topc(k1_pre_topc(A_108, B_109)) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.84/1.84  tff(c_365, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3' | ~v1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_73, c_359])).
% 4.84/1.84  tff(c_372, plain, (k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_62, c_365])).
% 4.84/1.84  tff(c_448, plain, (![A_117, B_118, C_119]: ('#skF_1'(A_117, B_118, C_119)=C_119 | v2_compts_1(C_119, A_117) | ~r1_tarski(C_119, k2_struct_0(B_118)) | ~m1_subset_1(C_119, k1_zfmisc_1(u1_struct_0(A_117))) | ~m1_pre_topc(B_118, A_117) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.84/1.84  tff(c_710, plain, (![A_147, C_148]: ('#skF_1'(A_147, k1_pre_topc('#skF_2', '#skF_3'), C_148)=C_148 | v2_compts_1(C_148, A_147) | ~r1_tarski(C_148, '#skF_3') | ~m1_subset_1(C_148, k1_zfmisc_1(u1_struct_0(A_147))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), A_147) | ~l1_pre_topc(A_147))), inference(superposition, [status(thm), theory('equality')], [c_372, c_448])).
% 4.84/1.84  tff(c_722, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), '#skF_4')='#skF_4' | v2_compts_1('#skF_4', '#skF_2') | ~r1_tarski('#skF_4', '#skF_3') | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_710])).
% 4.84/1.84  tff(c_733, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), '#skF_4')='#skF_4' | v2_compts_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_73, c_38, c_722])).
% 4.84/1.84  tff(c_734, plain, ('#skF_1'('#skF_2', k1_pre_topc('#skF_2', '#skF_3'), '#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_34, c_733])).
% 4.84/1.84  tff(c_764, plain, (~v2_compts_1('#skF_4', k1_pre_topc('#skF_2', '#skF_3')) | v2_compts_1('#skF_4', '#skF_2') | ~r1_tarski('#skF_4', k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_734, c_18])).
% 4.84/1.84  tff(c_771, plain, (~v2_compts_1('#skF_4', k1_pre_topc('#skF_2', '#skF_3')) | v2_compts_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_73, c_42, c_38, c_372, c_764])).
% 4.84/1.84  tff(c_772, plain, (~v2_compts_1('#skF_4', k1_pre_topc('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_34, c_771])).
% 4.84/1.84  tff(c_40, plain, (v2_compts_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.84/1.84  tff(c_102, plain, (![C_77, A_78, B_79]: (m1_subset_1(C_77, k1_zfmisc_1(u1_struct_0(A_78))) | ~m1_subset_1(C_77, k1_zfmisc_1(u1_struct_0(B_79))) | ~m1_pre_topc(B_79, A_78) | ~l1_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.84/1.84  tff(c_108, plain, (![A_78]: (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_78))) | ~m1_pre_topc('#skF_2', A_78) | ~l1_pre_topc(A_78))), inference(resolution, [status(thm)], [c_44, c_102])).
% 4.84/1.84  tff(c_197, plain, (![B_96, A_97]: (v2_compts_1(B_96, A_97) | ~v1_compts_1(k1_pre_topc(A_97, B_96)) | k1_xboole_0=B_96 | ~v2_pre_topc(A_97) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_pre_topc(A_97))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.84/1.84  tff(c_210, plain, (![A_78]: (v2_compts_1('#skF_3', A_78) | ~v1_compts_1(k1_pre_topc(A_78, '#skF_3')) | k1_xboole_0='#skF_3' | ~v2_pre_topc(A_78) | ~m1_pre_topc('#skF_2', A_78) | ~l1_pre_topc(A_78))), inference(resolution, [status(thm)], [c_108, c_197])).
% 4.84/1.84  tff(c_220, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_210])).
% 4.84/1.84  tff(c_30, plain, (![A_57]: (v1_compts_1(k1_pre_topc(A_57, k1_xboole_0)) | ~v2_compts_1(k1_xboole_0, A_57) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.84/1.84  tff(c_313, plain, (![A_104]: (v1_compts_1(k1_pre_topc(A_104, '#skF_3')) | ~v2_compts_1('#skF_3', A_104) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_220, c_220, c_30])).
% 4.84/1.84  tff(c_319, plain, (v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_313])).
% 4.84/1.84  tff(c_323, plain, (v1_compts_1(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_40, c_319])).
% 4.84/1.84  tff(c_22, plain, (![A_35, B_47, C_53]: (m1_subset_1('#skF_1'(A_35, B_47, C_53), k1_zfmisc_1(u1_struct_0(B_47))) | v2_compts_1(C_53, A_35) | ~r1_tarski(C_53, k2_struct_0(B_47)) | ~m1_subset_1(C_53, k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_pre_topc(B_47, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.84/1.84  tff(c_762, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2', '#skF_3')))) | v2_compts_1('#skF_4', '#skF_2') | ~r1_tarski('#skF_4', k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_734, c_22])).
% 4.84/1.84  tff(c_768, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2', '#skF_3')))) | v2_compts_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_73, c_42, c_38, c_372, c_762])).
% 4.84/1.84  tff(c_769, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_34, c_768])).
% 4.84/1.84  tff(c_32, plain, (![B_62, A_60]: (v2_compts_1(B_62, A_60) | ~v4_pre_topc(B_62, A_60) | ~v1_compts_1(A_60) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.84/1.84  tff(c_799, plain, (v2_compts_1('#skF_4', k1_pre_topc('#skF_2', '#skF_3')) | ~v4_pre_topc('#skF_4', k1_pre_topc('#skF_2', '#skF_3')) | ~v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_769, c_32])).
% 4.84/1.84  tff(c_836, plain, (v2_compts_1('#skF_4', k1_pre_topc('#skF_2', '#skF_3')) | ~v4_pre_topc('#skF_4', k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_323, c_799])).
% 4.84/1.84  tff(c_837, plain, (~v4_pre_topc('#skF_4', k1_pre_topc('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_772, c_836])).
% 4.84/1.84  tff(c_14, plain, (![D_34, C_32, A_20]: (v4_pre_topc(D_34, C_32) | ~m1_subset_1(D_34, k1_zfmisc_1(u1_struct_0(C_32))) | ~v4_pre_topc(D_34, A_20) | ~m1_pre_topc(C_32, A_20) | ~m1_subset_1(D_34, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.84/1.84  tff(c_824, plain, (![A_20]: (v4_pre_topc('#skF_4', k1_pre_topc('#skF_2', '#skF_3')) | ~v4_pre_topc('#skF_4', A_20) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), A_20) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(resolution, [status(thm)], [c_769, c_14])).
% 4.84/1.84  tff(c_1231, plain, (![A_177]: (~v4_pre_topc('#skF_4', A_177) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), A_177) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177))), inference(negUnitSimplification, [status(thm)], [c_837, c_824])).
% 4.84/1.84  tff(c_1243, plain, (~v4_pre_topc('#skF_4', '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_1231])).
% 4.84/1.84  tff(c_1252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_73, c_36, c_1243])).
% 4.84/1.84  tff(c_1254, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_210])).
% 4.84/1.84  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.84/1.84  tff(c_1257, plain, (![A_179, B_180]: (v1_compts_1(k1_pre_topc(A_179, B_180)) | ~v2_compts_1(B_180, A_179) | k1_xboole_0=B_180 | ~v2_pre_topc(A_179) | ~m1_subset_1(B_180, k1_zfmisc_1(u1_struct_0(A_179))) | ~l1_pre_topc(A_179))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.84/1.84  tff(c_1269, plain, (v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_compts_1('#skF_3', '#skF_2') | k1_xboole_0='#skF_3' | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_44, c_1257])).
% 4.84/1.84  tff(c_1280, plain, (v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_40, c_1269])).
% 4.84/1.84  tff(c_1281, plain, (v1_compts_1(k1_pre_topc('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1254, c_1280])).
% 4.84/1.84  tff(c_1799, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2', '#skF_3')))) | v2_compts_1('#skF_4', '#skF_2') | ~r1_tarski('#skF_4', k2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1786, c_22])).
% 4.84/1.84  tff(c_1810, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2', '#skF_3')))) | v2_compts_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_73, c_42, c_38, c_1428, c_1799])).
% 4.84/1.84  tff(c_1811, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_34, c_1810])).
% 4.84/1.84  tff(c_1847, plain, (v2_compts_1('#skF_4', k1_pre_topc('#skF_2', '#skF_3')) | ~v4_pre_topc('#skF_4', k1_pre_topc('#skF_2', '#skF_3')) | ~v1_compts_1(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1811, c_32])).
% 4.84/1.84  tff(c_1891, plain, (v2_compts_1('#skF_4', k1_pre_topc('#skF_2', '#skF_3')) | ~v4_pre_topc('#skF_4', k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_1281, c_1847])).
% 4.84/1.84  tff(c_1892, plain, (~v4_pre_topc('#skF_4', k1_pre_topc('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1814, c_1891])).
% 4.84/1.84  tff(c_1880, plain, (![A_20]: (v4_pre_topc('#skF_4', k1_pre_topc('#skF_2', '#skF_3')) | ~v4_pre_topc('#skF_4', A_20) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), A_20) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(resolution, [status(thm)], [c_1811, c_14])).
% 4.84/1.84  tff(c_2279, plain, (![A_261]: (~v4_pre_topc('#skF_4', A_261) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), A_261) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_261))) | ~l1_pre_topc(A_261))), inference(negUnitSimplification, [status(thm)], [c_1892, c_1880])).
% 4.84/1.84  tff(c_2291, plain, (~v4_pre_topc('#skF_4', '#skF_2') | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_2279])).
% 4.84/1.84  tff(c_2300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_73, c_36, c_2291])).
% 4.84/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.84/1.84  
% 4.84/1.84  Inference rules
% 4.84/1.84  ----------------------
% 4.84/1.84  #Ref     : 0
% 4.84/1.84  #Sup     : 457
% 4.84/1.84  #Fact    : 0
% 4.84/1.84  #Define  : 0
% 4.84/1.84  #Split   : 23
% 4.84/1.84  #Chain   : 0
% 4.84/1.84  #Close   : 0
% 4.84/1.84  
% 4.84/1.84  Ordering : KBO
% 4.84/1.84  
% 4.84/1.84  Simplification rules
% 4.84/1.84  ----------------------
% 4.84/1.84  #Subsume      : 144
% 4.84/1.84  #Demod        : 479
% 4.84/1.84  #Tautology    : 91
% 4.84/1.84  #SimpNegUnit  : 72
% 4.84/1.84  #BackRed      : 24
% 4.84/1.84  
% 4.84/1.84  #Partial instantiations: 0
% 4.84/1.84  #Strategies tried      : 1
% 4.84/1.84  
% 4.84/1.84  Timing (in seconds)
% 4.84/1.84  ----------------------
% 4.84/1.84  Preprocessing        : 0.32
% 4.84/1.84  Parsing              : 0.18
% 4.84/1.84  CNF conversion       : 0.03
% 4.84/1.84  Main loop            : 0.74
% 4.84/1.84  Inferencing          : 0.24
% 4.84/1.84  Reduction            : 0.24
% 4.84/1.84  Demodulation         : 0.16
% 4.84/1.84  BG Simplification    : 0.03
% 4.84/1.84  Subsumption          : 0.19
% 4.84/1.84  Abstraction          : 0.03
% 4.84/1.84  MUC search           : 0.00
% 4.84/1.84  Cooper               : 0.00
% 4.84/1.84  Total                : 1.10
% 4.84/1.84  Index Insertion      : 0.00
% 4.84/1.84  Index Deletion       : 0.00
% 4.84/1.84  Index Matching       : 0.00
% 4.84/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
