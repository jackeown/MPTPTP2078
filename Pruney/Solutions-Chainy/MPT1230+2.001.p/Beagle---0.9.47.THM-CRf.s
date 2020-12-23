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
% DateTime   : Thu Dec  3 10:20:29 EST 2020

% Result     : Theorem 4.82s
% Output     : CNFRefutation 4.82s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 250 expanded)
%              Number of leaves         :   28 (  97 expanded)
%              Depth                    :   16
%              Number of atoms          :  211 (1100 expanded)
%              Number of equality atoms :    1 (  12 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_hidden(C,k2_pre_topc(A,B))
                <=> ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                     => ~ ( v3_pre_topc(D,A)
                          & r2_hidden(C,D)
                          & r1_xboole_0(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tops_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = k2_pre_topc(A,B)
              <=> ! [D] :
                    ( r2_hidden(D,u1_struct_0(A))
                   => ( r2_hidden(D,C)
                    <=> ! [E] :
                          ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                         => ~ ( v3_pre_topc(E,A)
                              & r2_hidden(D,E)
                              & r1_xboole_0(B,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_46,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38,plain,(
    ! [A_89] :
      ( l1_struct_0(A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_hidden(A_1,B_2)
      | v1_xboole_0(B_2)
      | ~ m1_subset_1(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_36,plain,(
    ! [A_87,B_88] :
      ( m1_subset_1(k2_pre_topc(A_87,B_88),k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_52,plain,
    ( r1_xboole_0('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_73,plain,(
    ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_1007,plain,(
    ! [D_433,A_434,B_435] :
      ( r2_hidden(D_433,'#skF_1'(A_434,B_435,k2_pre_topc(A_434,B_435),D_433))
      | r2_hidden(D_433,k2_pre_topc(A_434,B_435))
      | ~ r2_hidden(D_433,u1_struct_0(A_434))
      | ~ m1_subset_1(k2_pre_topc(A_434,B_435),k1_zfmisc_1(u1_struct_0(A_434)))
      | ~ m1_subset_1(B_435,k1_zfmisc_1(u1_struct_0(A_434)))
      | ~ l1_pre_topc(A_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1010,plain,(
    ! [D_433,A_87,B_88] :
      ( r2_hidden(D_433,'#skF_1'(A_87,B_88,k2_pre_topc(A_87,B_88),D_433))
      | r2_hidden(D_433,k2_pre_topc(A_87,B_88))
      | ~ r2_hidden(D_433,u1_struct_0(A_87))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_36,c_1007])).

tff(c_1003,plain,(
    ! [A_430,B_431,D_432] :
      ( v3_pre_topc('#skF_1'(A_430,B_431,k2_pre_topc(A_430,B_431),D_432),A_430)
      | r2_hidden(D_432,k2_pre_topc(A_430,B_431))
      | ~ r2_hidden(D_432,u1_struct_0(A_430))
      | ~ m1_subset_1(k2_pre_topc(A_430,B_431),k1_zfmisc_1(u1_struct_0(A_430)))
      | ~ m1_subset_1(B_431,k1_zfmisc_1(u1_struct_0(A_430)))
      | ~ l1_pre_topc(A_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1006,plain,(
    ! [A_87,B_88,D_432] :
      ( v3_pre_topc('#skF_1'(A_87,B_88,k2_pre_topc(A_87,B_88),D_432),A_87)
      | r2_hidden(D_432,k2_pre_topc(A_87,B_88))
      | ~ r2_hidden(D_432,u1_struct_0(A_87))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_36,c_1003])).

tff(c_1014,plain,(
    ! [A_445,B_446,D_447] :
      ( m1_subset_1('#skF_1'(A_445,B_446,k2_pre_topc(A_445,B_446),D_447),k1_zfmisc_1(u1_struct_0(A_445)))
      | r2_hidden(D_447,k2_pre_topc(A_445,B_446))
      | ~ r2_hidden(D_447,u1_struct_0(A_445))
      | ~ m1_subset_1(k2_pre_topc(A_445,B_446),k1_zfmisc_1(u1_struct_0(A_445)))
      | ~ m1_subset_1(B_446,k1_zfmisc_1(u1_struct_0(A_445)))
      | ~ l1_pre_topc(A_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_70,plain,(
    ! [D_109] :
      ( r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5'))
      | ~ r1_xboole_0('#skF_5',D_109)
      | ~ r2_hidden('#skF_6',D_109)
      | ~ v3_pre_topc(D_109,'#skF_4')
      | ~ m1_subset_1(D_109,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_899,plain,(
    ! [D_109] :
      ( ~ r1_xboole_0('#skF_5',D_109)
      | ~ r2_hidden('#skF_6',D_109)
      | ~ v3_pre_topc(D_109,'#skF_4')
      | ~ m1_subset_1(D_109,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_70])).

tff(c_1026,plain,(
    ! [B_446,D_447] :
      ( ~ r1_xboole_0('#skF_5','#skF_1'('#skF_4',B_446,k2_pre_topc('#skF_4',B_446),D_447))
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_446,k2_pre_topc('#skF_4',B_446),D_447))
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_446,k2_pre_topc('#skF_4',B_446),D_447),'#skF_4')
      | r2_hidden(D_447,k2_pre_topc('#skF_4',B_446))
      | ~ r2_hidden(D_447,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',B_446),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_446,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1014,c_899])).

tff(c_1102,plain,(
    ! [B_474,D_475] :
      ( ~ r1_xboole_0('#skF_5','#skF_1'('#skF_4',B_474,k2_pre_topc('#skF_4',B_474),D_475))
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_474,k2_pre_topc('#skF_4',B_474),D_475))
      | ~ v3_pre_topc('#skF_1'('#skF_4',B_474,k2_pre_topc('#skF_4',B_474),D_475),'#skF_4')
      | r2_hidden(D_475,k2_pre_topc('#skF_4',B_474))
      | ~ r2_hidden(D_475,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',B_474),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_474,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1026])).

tff(c_1105,plain,(
    ! [B_88,D_432] :
      ( ~ r1_xboole_0('#skF_5','#skF_1'('#skF_4',B_88,k2_pre_topc('#skF_4',B_88),D_432))
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_88,k2_pre_topc('#skF_4',B_88),D_432))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',B_88),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden(D_432,k2_pre_topc('#skF_4',B_88))
      | ~ r2_hidden(D_432,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1006,c_1102])).

tff(c_1110,plain,(
    ! [B_479,D_480] :
      ( ~ r1_xboole_0('#skF_5','#skF_1'('#skF_4',B_479,k2_pre_topc('#skF_4',B_479),D_480))
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_4',B_479,k2_pre_topc('#skF_4',B_479),D_480))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',B_479),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden(D_480,k2_pre_topc('#skF_4',B_479))
      | ~ r2_hidden(D_480,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_479,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1105])).

tff(c_1113,plain,(
    ! [B_88] :
      ( ~ r1_xboole_0('#skF_5','#skF_1'('#skF_4',B_88,k2_pre_topc('#skF_4',B_88),'#skF_6'))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',B_88),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden('#skF_6',k2_pre_topc('#skF_4',B_88))
      | ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1010,c_1110])).

tff(c_1119,plain,(
    ! [B_88] :
      ( ~ r1_xboole_0('#skF_5','#skF_1'('#skF_4',B_88,k2_pre_topc('#skF_4',B_88),'#skF_6'))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',B_88),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden('#skF_6',k2_pre_topc('#skF_4',B_88))
      | ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1113])).

tff(c_1121,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1119])).

tff(c_1124,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2,c_1121])).

tff(c_1127,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1124])).

tff(c_40,plain,(
    ! [A_90] :
      ( ~ v1_xboole_0(u1_struct_0(A_90))
      | ~ l1_struct_0(A_90)
      | v2_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1130,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1127,c_40])).

tff(c_1133,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1130])).

tff(c_1151,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_1133])).

tff(c_1155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1151])).

tff(c_1157,plain,(
    r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1119])).

tff(c_998,plain,(
    ! [B_424,A_425,D_426] :
      ( r1_xboole_0(B_424,'#skF_1'(A_425,B_424,k2_pre_topc(A_425,B_424),D_426))
      | r2_hidden(D_426,k2_pre_topc(A_425,B_424))
      | ~ r2_hidden(D_426,u1_struct_0(A_425))
      | ~ m1_subset_1(k2_pre_topc(A_425,B_424),k1_zfmisc_1(u1_struct_0(A_425)))
      | ~ m1_subset_1(B_424,k1_zfmisc_1(u1_struct_0(A_425)))
      | ~ l1_pre_topc(A_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1001,plain,(
    ! [B_88,A_87,D_426] :
      ( r1_xboole_0(B_88,'#skF_1'(A_87,B_88,k2_pre_topc(A_87,B_88),D_426))
      | r2_hidden(D_426,k2_pre_topc(A_87,B_88))
      | ~ r2_hidden(D_426,u1_struct_0(A_87))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_36,c_998])).

tff(c_1163,plain,(
    ! [B_485] :
      ( ~ r1_xboole_0('#skF_5','#skF_1'('#skF_4',B_485,k2_pre_topc('#skF_4',B_485),'#skF_6'))
      | ~ m1_subset_1(k2_pre_topc('#skF_4',B_485),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r2_hidden('#skF_6',k2_pre_topc('#skF_4',B_485))
      | ~ m1_subset_1(B_485,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_1119])).

tff(c_1166,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5'))
    | ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1001,c_1163])).

tff(c_1169,plain,
    ( ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1157,c_1166])).

tff(c_1170,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_1169])).

tff(c_1173,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1170])).

tff(c_1177,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1173])).

tff(c_1179,plain,(
    r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_58,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1186,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1179,c_58])).

tff(c_56,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1184,plain,(
    v3_pre_topc('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1179,c_56])).

tff(c_54,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_6',k2_pre_topc('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1182,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1179,c_54])).

tff(c_1178,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1284,plain,(
    ! [B_541,E_542,D_543,A_544] :
      ( ~ r1_xboole_0(B_541,E_542)
      | ~ r2_hidden(D_543,E_542)
      | ~ v3_pre_topc(E_542,A_544)
      | ~ m1_subset_1(E_542,k1_zfmisc_1(u1_struct_0(A_544)))
      | ~ r2_hidden(D_543,k2_pre_topc(A_544,B_541))
      | ~ r2_hidden(D_543,u1_struct_0(A_544))
      | ~ m1_subset_1(k2_pre_topc(A_544,B_541),k1_zfmisc_1(u1_struct_0(A_544)))
      | ~ m1_subset_1(B_541,k1_zfmisc_1(u1_struct_0(A_544)))
      | ~ l1_pre_topc(A_544) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1306,plain,(
    ! [D_549,A_550] :
      ( ~ r2_hidden(D_549,'#skF_7')
      | ~ v3_pre_topc('#skF_7',A_550)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(A_550)))
      | ~ r2_hidden(D_549,k2_pre_topc(A_550,'#skF_5'))
      | ~ r2_hidden(D_549,u1_struct_0(A_550))
      | ~ m1_subset_1(k2_pre_topc(A_550,'#skF_5'),k1_zfmisc_1(u1_struct_0(A_550)))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_550)))
      | ~ l1_pre_topc(A_550) ) ),
    inference(resolution,[status(thm)],[c_1178,c_1284])).

tff(c_1311,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | ~ v3_pre_topc('#skF_7','#skF_4')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1179,c_1306])).

tff(c_1315,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1186,c_1184,c_1182,c_1311])).

tff(c_1316,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_4','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1315])).

tff(c_1319,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1316])).

tff(c_1323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1319])).

tff(c_1324,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1315])).

tff(c_1336,plain,
    ( v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_2,c_1324])).

tff(c_1339,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1336])).

tff(c_1342,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1339,c_40])).

tff(c_1345,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1342])).

tff(c_1348,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_1345])).

tff(c_1352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1348])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:25:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.82/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.86  
% 4.82/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.86  %$ v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.82/1.86  
% 4.82/1.86  %Foreground sorts:
% 4.82/1.86  
% 4.82/1.86  
% 4.82/1.86  %Background operators:
% 4.82/1.86  
% 4.82/1.86  
% 4.82/1.86  %Foreground operators:
% 4.82/1.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.82/1.86  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.82/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.82/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.82/1.86  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.82/1.86  tff('#skF_7', type, '#skF_7': $i).
% 4.82/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.82/1.86  tff('#skF_6', type, '#skF_6': $i).
% 4.82/1.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.82/1.86  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.82/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.82/1.86  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.82/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.82/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.82/1.86  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.82/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.82/1.86  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.82/1.86  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.82/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.82/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.82/1.86  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.82/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.82/1.86  
% 4.82/1.89  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~((v3_pre_topc(D, A) & r2_hidden(C, D)) & r1_xboole_0(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_tops_1)).
% 4.82/1.89  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.82/1.89  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.82/1.89  tff(f_62, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.82/1.89  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k2_pre_topc(A, B)) <=> (![D]: (r2_hidden(D, u1_struct_0(A)) => (r2_hidden(D, C) <=> (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ~((v3_pre_topc(E, A) & r2_hidden(D, E)) & r1_xboole_0(B, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_pre_topc)).
% 4.82/1.89  tff(f_74, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.82/1.89  tff(c_46, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.82/1.89  tff(c_38, plain, (![A_89]: (l1_struct_0(A_89) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.82/1.89  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.82/1.89  tff(c_42, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.82/1.89  tff(c_2, plain, (![A_1, B_2]: (r2_hidden(A_1, B_2) | v1_xboole_0(B_2) | ~m1_subset_1(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.82/1.89  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.82/1.89  tff(c_36, plain, (![A_87, B_88]: (m1_subset_1(k2_pre_topc(A_87, B_88), k1_zfmisc_1(u1_struct_0(A_87))) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.82/1.89  tff(c_52, plain, (r1_xboole_0('#skF_5', '#skF_7') | ~r2_hidden('#skF_6', k2_pre_topc('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.82/1.89  tff(c_73, plain, (~r2_hidden('#skF_6', k2_pre_topc('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_52])).
% 4.82/1.89  tff(c_1007, plain, (![D_433, A_434, B_435]: (r2_hidden(D_433, '#skF_1'(A_434, B_435, k2_pre_topc(A_434, B_435), D_433)) | r2_hidden(D_433, k2_pre_topc(A_434, B_435)) | ~r2_hidden(D_433, u1_struct_0(A_434)) | ~m1_subset_1(k2_pre_topc(A_434, B_435), k1_zfmisc_1(u1_struct_0(A_434))) | ~m1_subset_1(B_435, k1_zfmisc_1(u1_struct_0(A_434))) | ~l1_pre_topc(A_434))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.82/1.89  tff(c_1010, plain, (![D_433, A_87, B_88]: (r2_hidden(D_433, '#skF_1'(A_87, B_88, k2_pre_topc(A_87, B_88), D_433)) | r2_hidden(D_433, k2_pre_topc(A_87, B_88)) | ~r2_hidden(D_433, u1_struct_0(A_87)) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(resolution, [status(thm)], [c_36, c_1007])).
% 4.82/1.89  tff(c_1003, plain, (![A_430, B_431, D_432]: (v3_pre_topc('#skF_1'(A_430, B_431, k2_pre_topc(A_430, B_431), D_432), A_430) | r2_hidden(D_432, k2_pre_topc(A_430, B_431)) | ~r2_hidden(D_432, u1_struct_0(A_430)) | ~m1_subset_1(k2_pre_topc(A_430, B_431), k1_zfmisc_1(u1_struct_0(A_430))) | ~m1_subset_1(B_431, k1_zfmisc_1(u1_struct_0(A_430))) | ~l1_pre_topc(A_430))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.82/1.89  tff(c_1006, plain, (![A_87, B_88, D_432]: (v3_pre_topc('#skF_1'(A_87, B_88, k2_pre_topc(A_87, B_88), D_432), A_87) | r2_hidden(D_432, k2_pre_topc(A_87, B_88)) | ~r2_hidden(D_432, u1_struct_0(A_87)) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(resolution, [status(thm)], [c_36, c_1003])).
% 4.82/1.89  tff(c_1014, plain, (![A_445, B_446, D_447]: (m1_subset_1('#skF_1'(A_445, B_446, k2_pre_topc(A_445, B_446), D_447), k1_zfmisc_1(u1_struct_0(A_445))) | r2_hidden(D_447, k2_pre_topc(A_445, B_446)) | ~r2_hidden(D_447, u1_struct_0(A_445)) | ~m1_subset_1(k2_pre_topc(A_445, B_446), k1_zfmisc_1(u1_struct_0(A_445))) | ~m1_subset_1(B_446, k1_zfmisc_1(u1_struct_0(A_445))) | ~l1_pre_topc(A_445))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.82/1.89  tff(c_70, plain, (![D_109]: (r2_hidden('#skF_6', k2_pre_topc('#skF_4', '#skF_5')) | ~r1_xboole_0('#skF_5', D_109) | ~r2_hidden('#skF_6', D_109) | ~v3_pre_topc(D_109, '#skF_4') | ~m1_subset_1(D_109, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.82/1.89  tff(c_899, plain, (![D_109]: (~r1_xboole_0('#skF_5', D_109) | ~r2_hidden('#skF_6', D_109) | ~v3_pre_topc(D_109, '#skF_4') | ~m1_subset_1(D_109, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_73, c_70])).
% 4.82/1.89  tff(c_1026, plain, (![B_446, D_447]: (~r1_xboole_0('#skF_5', '#skF_1'('#skF_4', B_446, k2_pre_topc('#skF_4', B_446), D_447)) | ~r2_hidden('#skF_6', '#skF_1'('#skF_4', B_446, k2_pre_topc('#skF_4', B_446), D_447)) | ~v3_pre_topc('#skF_1'('#skF_4', B_446, k2_pre_topc('#skF_4', B_446), D_447), '#skF_4') | r2_hidden(D_447, k2_pre_topc('#skF_4', B_446)) | ~r2_hidden(D_447, u1_struct_0('#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_4', B_446), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_446, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_1014, c_899])).
% 4.82/1.89  tff(c_1102, plain, (![B_474, D_475]: (~r1_xboole_0('#skF_5', '#skF_1'('#skF_4', B_474, k2_pre_topc('#skF_4', B_474), D_475)) | ~r2_hidden('#skF_6', '#skF_1'('#skF_4', B_474, k2_pre_topc('#skF_4', B_474), D_475)) | ~v3_pre_topc('#skF_1'('#skF_4', B_474, k2_pre_topc('#skF_4', B_474), D_475), '#skF_4') | r2_hidden(D_475, k2_pre_topc('#skF_4', B_474)) | ~r2_hidden(D_475, u1_struct_0('#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_4', B_474), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_474, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1026])).
% 4.82/1.89  tff(c_1105, plain, (![B_88, D_432]: (~r1_xboole_0('#skF_5', '#skF_1'('#skF_4', B_88, k2_pre_topc('#skF_4', B_88), D_432)) | ~r2_hidden('#skF_6', '#skF_1'('#skF_4', B_88, k2_pre_topc('#skF_4', B_88), D_432)) | ~m1_subset_1(k2_pre_topc('#skF_4', B_88), k1_zfmisc_1(u1_struct_0('#skF_4'))) | r2_hidden(D_432, k2_pre_topc('#skF_4', B_88)) | ~r2_hidden(D_432, u1_struct_0('#skF_4')) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_1006, c_1102])).
% 4.82/1.89  tff(c_1110, plain, (![B_479, D_480]: (~r1_xboole_0('#skF_5', '#skF_1'('#skF_4', B_479, k2_pre_topc('#skF_4', B_479), D_480)) | ~r2_hidden('#skF_6', '#skF_1'('#skF_4', B_479, k2_pre_topc('#skF_4', B_479), D_480)) | ~m1_subset_1(k2_pre_topc('#skF_4', B_479), k1_zfmisc_1(u1_struct_0('#skF_4'))) | r2_hidden(D_480, k2_pre_topc('#skF_4', B_479)) | ~r2_hidden(D_480, u1_struct_0('#skF_4')) | ~m1_subset_1(B_479, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1105])).
% 4.82/1.89  tff(c_1113, plain, (![B_88]: (~r1_xboole_0('#skF_5', '#skF_1'('#skF_4', B_88, k2_pre_topc('#skF_4', B_88), '#skF_6')) | ~m1_subset_1(k2_pre_topc('#skF_4', B_88), k1_zfmisc_1(u1_struct_0('#skF_4'))) | r2_hidden('#skF_6', k2_pre_topc('#skF_4', B_88)) | ~r2_hidden('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_1010, c_1110])).
% 4.82/1.89  tff(c_1119, plain, (![B_88]: (~r1_xboole_0('#skF_5', '#skF_1'('#skF_4', B_88, k2_pre_topc('#skF_4', B_88), '#skF_6')) | ~m1_subset_1(k2_pre_topc('#skF_4', B_88), k1_zfmisc_1(u1_struct_0('#skF_4'))) | r2_hidden('#skF_6', k2_pre_topc('#skF_4', B_88)) | ~r2_hidden('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1113])).
% 4.82/1.89  tff(c_1121, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_1119])).
% 4.82/1.89  tff(c_1124, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2, c_1121])).
% 4.82/1.89  tff(c_1127, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1124])).
% 4.82/1.89  tff(c_40, plain, (![A_90]: (~v1_xboole_0(u1_struct_0(A_90)) | ~l1_struct_0(A_90) | v2_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.82/1.89  tff(c_1130, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1127, c_40])).
% 4.82/1.89  tff(c_1133, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_1130])).
% 4.82/1.89  tff(c_1151, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_38, c_1133])).
% 4.82/1.89  tff(c_1155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_1151])).
% 4.82/1.89  tff(c_1157, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1119])).
% 4.82/1.89  tff(c_998, plain, (![B_424, A_425, D_426]: (r1_xboole_0(B_424, '#skF_1'(A_425, B_424, k2_pre_topc(A_425, B_424), D_426)) | r2_hidden(D_426, k2_pre_topc(A_425, B_424)) | ~r2_hidden(D_426, u1_struct_0(A_425)) | ~m1_subset_1(k2_pre_topc(A_425, B_424), k1_zfmisc_1(u1_struct_0(A_425))) | ~m1_subset_1(B_424, k1_zfmisc_1(u1_struct_0(A_425))) | ~l1_pre_topc(A_425))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.82/1.89  tff(c_1001, plain, (![B_88, A_87, D_426]: (r1_xboole_0(B_88, '#skF_1'(A_87, B_88, k2_pre_topc(A_87, B_88), D_426)) | r2_hidden(D_426, k2_pre_topc(A_87, B_88)) | ~r2_hidden(D_426, u1_struct_0(A_87)) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87))), inference(resolution, [status(thm)], [c_36, c_998])).
% 4.82/1.89  tff(c_1163, plain, (![B_485]: (~r1_xboole_0('#skF_5', '#skF_1'('#skF_4', B_485, k2_pre_topc('#skF_4', B_485), '#skF_6')) | ~m1_subset_1(k2_pre_topc('#skF_4', B_485), k1_zfmisc_1(u1_struct_0('#skF_4'))) | r2_hidden('#skF_6', k2_pre_topc('#skF_4', B_485)) | ~m1_subset_1(B_485, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_1119])).
% 4.82/1.89  tff(c_1166, plain, (~m1_subset_1(k2_pre_topc('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | r2_hidden('#skF_6', k2_pre_topc('#skF_4', '#skF_5')) | ~r2_hidden('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1001, c_1163])).
% 4.82/1.89  tff(c_1169, plain, (~m1_subset_1(k2_pre_topc('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | r2_hidden('#skF_6', k2_pre_topc('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1157, c_1166])).
% 4.82/1.89  tff(c_1170, plain, (~m1_subset_1(k2_pre_topc('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_73, c_1169])).
% 4.82/1.89  tff(c_1173, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1170])).
% 4.82/1.89  tff(c_1177, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1173])).
% 4.82/1.89  tff(c_1179, plain, (r2_hidden('#skF_6', k2_pre_topc('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_52])).
% 4.82/1.89  tff(c_58, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden('#skF_6', k2_pre_topc('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.82/1.89  tff(c_1186, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1179, c_58])).
% 4.82/1.89  tff(c_56, plain, (v3_pre_topc('#skF_7', '#skF_4') | ~r2_hidden('#skF_6', k2_pre_topc('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.82/1.89  tff(c_1184, plain, (v3_pre_topc('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1179, c_56])).
% 4.82/1.89  tff(c_54, plain, (r2_hidden('#skF_6', '#skF_7') | ~r2_hidden('#skF_6', k2_pre_topc('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.82/1.89  tff(c_1182, plain, (r2_hidden('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1179, c_54])).
% 4.82/1.89  tff(c_1178, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_52])).
% 4.82/1.89  tff(c_1284, plain, (![B_541, E_542, D_543, A_544]: (~r1_xboole_0(B_541, E_542) | ~r2_hidden(D_543, E_542) | ~v3_pre_topc(E_542, A_544) | ~m1_subset_1(E_542, k1_zfmisc_1(u1_struct_0(A_544))) | ~r2_hidden(D_543, k2_pre_topc(A_544, B_541)) | ~r2_hidden(D_543, u1_struct_0(A_544)) | ~m1_subset_1(k2_pre_topc(A_544, B_541), k1_zfmisc_1(u1_struct_0(A_544))) | ~m1_subset_1(B_541, k1_zfmisc_1(u1_struct_0(A_544))) | ~l1_pre_topc(A_544))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.82/1.89  tff(c_1306, plain, (![D_549, A_550]: (~r2_hidden(D_549, '#skF_7') | ~v3_pre_topc('#skF_7', A_550) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(A_550))) | ~r2_hidden(D_549, k2_pre_topc(A_550, '#skF_5')) | ~r2_hidden(D_549, u1_struct_0(A_550)) | ~m1_subset_1(k2_pre_topc(A_550, '#skF_5'), k1_zfmisc_1(u1_struct_0(A_550))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_550))) | ~l1_pre_topc(A_550))), inference(resolution, [status(thm)], [c_1178, c_1284])).
% 4.82/1.89  tff(c_1311, plain, (~r2_hidden('#skF_6', '#skF_7') | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1179, c_1306])).
% 4.82/1.89  tff(c_1315, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(k2_pre_topc('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1186, c_1184, c_1182, c_1311])).
% 4.82/1.89  tff(c_1316, plain, (~m1_subset_1(k2_pre_topc('#skF_4', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_1315])).
% 4.82/1.89  tff(c_1319, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1316])).
% 4.82/1.89  tff(c_1323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1319])).
% 4.82/1.89  tff(c_1324, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1315])).
% 4.82/1.89  tff(c_1336, plain, (v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_2, c_1324])).
% 4.82/1.89  tff(c_1339, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1336])).
% 4.82/1.89  tff(c_1342, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1339, c_40])).
% 4.82/1.89  tff(c_1345, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_1342])).
% 4.82/1.89  tff(c_1348, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_38, c_1345])).
% 4.82/1.89  tff(c_1352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_1348])).
% 4.82/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.89  
% 4.82/1.89  Inference rules
% 4.82/1.89  ----------------------
% 4.82/1.89  #Ref     : 0
% 4.82/1.89  #Sup     : 248
% 4.82/1.89  #Fact    : 0
% 4.82/1.89  #Define  : 0
% 4.82/1.89  #Split   : 24
% 4.82/1.89  #Chain   : 0
% 4.82/1.89  #Close   : 0
% 4.82/1.89  
% 4.82/1.89  Ordering : KBO
% 4.82/1.89  
% 4.82/1.89  Simplification rules
% 4.82/1.89  ----------------------
% 4.82/1.89  #Subsume      : 56
% 4.82/1.89  #Demod        : 102
% 4.82/1.89  #Tautology    : 17
% 4.82/1.89  #SimpNegUnit  : 13
% 4.82/1.89  #BackRed      : 0
% 4.82/1.89  
% 4.82/1.89  #Partial instantiations: 0
% 4.82/1.89  #Strategies tried      : 1
% 4.82/1.89  
% 4.82/1.89  Timing (in seconds)
% 4.82/1.89  ----------------------
% 4.82/1.90  Preprocessing        : 0.33
% 4.82/1.90  Parsing              : 0.17
% 4.82/1.90  CNF conversion       : 0.04
% 4.82/1.90  Main loop            : 0.74
% 4.82/1.90  Inferencing          : 0.29
% 4.82/1.90  Reduction            : 0.19
% 4.82/1.90  Demodulation         : 0.13
% 4.82/1.90  BG Simplification    : 0.04
% 4.82/1.90  Subsumption          : 0.18
% 4.82/1.90  Abstraction          : 0.04
% 4.82/1.90  MUC search           : 0.00
% 4.82/1.90  Cooper               : 0.00
% 4.82/1.90  Total                : 1.13
% 4.82/1.90  Index Insertion      : 0.00
% 4.82/1.90  Index Deletion       : 0.00
% 4.82/1.90  Index Matching       : 0.00
% 4.82/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
