%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:23 EST 2020

% Result     : Theorem 40.82s
% Output     : CNFRefutation 40.82s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 831 expanded)
%              Number of leaves         :   42 ( 296 expanded)
%              Depth                    :   21
%              Number of atoms          :  242 (1844 expanded)
%              Number of equality atoms :   43 ( 409 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k3_yellow_1 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_73,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_79,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_77,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
              & v2_waybel_0(B,k3_yellow_1(A))
              & v13_waybel_0(B,k3_yellow_1(A))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
           => ! [C] :
                ~ ( r2_hidden(C,B)
                  & v1_xboole_0(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))
     => ( v13_waybel_0(B,k3_yellow_1(A))
      <=> ! [C,D] :
            ( ( r1_tarski(C,D)
              & r1_tarski(D,A)
              & r2_hidden(C,B) )
           => r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_7)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_20,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_164,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(A_56,k1_zfmisc_1(B_57))
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_54,plain,(
    ! [B_29] :
      ( ~ v1_subset_1(B_29,B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_168,plain,(
    ! [B_57] :
      ( ~ v1_subset_1(B_57,B_57)
      | ~ r1_tarski(B_57,B_57) ) ),
    inference(resolution,[status(thm)],[c_164,c_54])).

tff(c_174,plain,(
    ! [B_57] : ~ v1_subset_1(B_57,B_57) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_168])).

tff(c_44,plain,(
    ! [A_25] : k9_setfam_1(A_25) = k1_zfmisc_1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_50,plain,(
    ! [A_27] : k2_yellow_1(k9_setfam_1(A_27)) = k3_yellow_1(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_103,plain,(
    ! [A_46] : k2_yellow_1(k1_zfmisc_1(A_46)) = k3_yellow_1(A_46) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_50])).

tff(c_46,plain,(
    ! [A_26] : u1_struct_0(k2_yellow_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_109,plain,(
    ! [A_46] : u1_struct_0(k3_yellow_1(A_46)) = k1_zfmisc_1(A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_46])).

tff(c_70,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_8')))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_137,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k1_zfmisc_1('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_70])).

tff(c_147,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(A_50,B_51)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_154,plain,(
    r1_tarski('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_137,c_147])).

tff(c_188,plain,(
    ! [B_63,A_64] :
      ( B_63 = A_64
      | ~ r1_tarski(B_63,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_195,plain,
    ( k1_zfmisc_1('#skF_8') = '#skF_9'
    | ~ r1_tarski(k1_zfmisc_1('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_154,c_188])).

tff(c_214,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_72,plain,(
    v13_waybel_0('#skF_9',k3_yellow_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_982,plain,(
    ! [A_143,B_144] :
      ( r2_hidden('#skF_2'(A_143,B_144),B_144)
      | r2_hidden('#skF_3'(A_143,B_144),A_143)
      | B_144 = A_143 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3536,plain,(
    ! [A_269,B_270,B_271] :
      ( r2_hidden('#skF_3'(A_269,B_270),B_271)
      | ~ r1_tarski(A_269,B_271)
      | r2_hidden('#skF_2'(A_269,B_270),B_270)
      | B_270 = A_269 ) ),
    inference(resolution,[status(thm)],[c_982,c_2])).

tff(c_37298,plain,(
    ! [A_863,B_864,B_865,B_866] :
      ( r2_hidden('#skF_3'(A_863,B_864),B_865)
      | ~ r1_tarski(B_866,B_865)
      | ~ r1_tarski(A_863,B_866)
      | r2_hidden('#skF_2'(A_863,B_864),B_864)
      | B_864 = A_863 ) ),
    inference(resolution,[status(thm)],[c_3536,c_2])).

tff(c_114640,plain,(
    ! [A_1689,B_1690] :
      ( r2_hidden('#skF_3'(A_1689,B_1690),k1_zfmisc_1('#skF_8'))
      | ~ r1_tarski(A_1689,'#skF_9')
      | r2_hidden('#skF_2'(A_1689,B_1690),B_1690)
      | B_1690 = A_1689 ) ),
    inference(resolution,[status(thm)],[c_154,c_37298])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_121909,plain,(
    ! [A_1741] :
      ( ~ r1_tarski(A_1741,'#skF_9')
      | r2_hidden('#skF_2'(A_1741,k1_zfmisc_1('#skF_8')),k1_zfmisc_1('#skF_8'))
      | k1_zfmisc_1('#skF_8') = A_1741 ) ),
    inference(resolution,[status(thm)],[c_114640,c_10])).

tff(c_22,plain,(
    ! [C_15,A_11] :
      ( r1_tarski(C_15,A_11)
      | ~ r2_hidden(C_15,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_121995,plain,(
    ! [A_1742] :
      ( r1_tarski('#skF_2'(A_1742,k1_zfmisc_1('#skF_8')),'#skF_8')
      | ~ r1_tarski(A_1742,'#skF_9')
      | k1_zfmisc_1('#skF_8') = A_1742 ) ),
    inference(resolution,[status(thm)],[c_121909,c_22])).

tff(c_66,plain,(
    v1_xboole_0('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_257,plain,(
    ! [C_73,B_74,A_75] :
      ( ~ v1_xboole_0(C_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(C_73))
      | ~ r2_hidden(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_276,plain,(
    ! [B_77,A_78,A_79] :
      ( ~ v1_xboole_0(B_77)
      | ~ r2_hidden(A_78,A_79)
      | ~ r1_tarski(A_79,B_77) ) ),
    inference(resolution,[status(thm)],[c_38,c_257])).

tff(c_296,plain,(
    ! [B_81,A_82,B_83] :
      ( ~ v1_xboole_0(B_81)
      | ~ r1_tarski(A_82,B_81)
      | r1_tarski(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_6,c_276])).

tff(c_307,plain,(
    ! [B_84,B_85] :
      ( ~ v1_xboole_0(B_84)
      | r1_tarski(B_84,B_85) ) ),
    inference(resolution,[status(thm)],[c_20,c_296])).

tff(c_34,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_155,plain,(
    ! [A_16] : r1_tarski(k1_xboole_0,A_16) ),
    inference(resolution,[status(thm)],[c_34,c_147])).

tff(c_196,plain,(
    ! [A_16] :
      ( k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_155,c_188])).

tff(c_328,plain,(
    ! [B_86] :
      ( k1_xboole_0 = B_86
      | ~ v1_xboole_0(B_86) ) ),
    inference(resolution,[status(thm)],[c_307,c_196])).

tff(c_332,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_66,c_328])).

tff(c_347,plain,(
    ! [A_16] : r1_tarski('#skF_10',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_155])).

tff(c_68,plain,(
    r2_hidden('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_56,plain,(
    ! [D_37,B_31,C_36,A_30] :
      ( r2_hidden(D_37,B_31)
      | ~ r2_hidden(C_36,B_31)
      | ~ r1_tarski(D_37,A_30)
      | ~ r1_tarski(C_36,D_37)
      | ~ v13_waybel_0(B_31,k3_yellow_1(A_30))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_30)))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2718,plain,(
    ! [D_234,B_235,C_236,A_237] :
      ( r2_hidden(D_234,B_235)
      | ~ r2_hidden(C_236,B_235)
      | ~ r1_tarski(D_234,A_237)
      | ~ r1_tarski(C_236,D_234)
      | ~ v13_waybel_0(B_235,k3_yellow_1(A_237))
      | ~ m1_subset_1(B_235,k1_zfmisc_1(k1_zfmisc_1(A_237))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_56])).

tff(c_2746,plain,(
    ! [D_234,A_237] :
      ( r2_hidden(D_234,'#skF_9')
      | ~ r1_tarski(D_234,A_237)
      | ~ r1_tarski('#skF_10',D_234)
      | ~ v13_waybel_0('#skF_9',k3_yellow_1(A_237))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k1_zfmisc_1(A_237))) ) ),
    inference(resolution,[status(thm)],[c_68,c_2718])).

tff(c_2766,plain,(
    ! [D_234,A_237] :
      ( r2_hidden(D_234,'#skF_9')
      | ~ r1_tarski(D_234,A_237)
      | ~ v13_waybel_0('#skF_9',k3_yellow_1(A_237))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k1_zfmisc_1(A_237))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_2746])).

tff(c_122151,plain,(
    ! [A_1742] :
      ( r2_hidden('#skF_2'(A_1742,k1_zfmisc_1('#skF_8')),'#skF_9')
      | ~ v13_waybel_0('#skF_9',k3_yellow_1('#skF_8'))
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k1_zfmisc_1('#skF_8')))
      | ~ r1_tarski(A_1742,'#skF_9')
      | k1_zfmisc_1('#skF_8') = A_1742 ) ),
    inference(resolution,[status(thm)],[c_121995,c_2766])).

tff(c_122282,plain,(
    ! [A_1743] :
      ( r2_hidden('#skF_2'(A_1743,k1_zfmisc_1('#skF_8')),'#skF_9')
      | ~ r1_tarski(A_1743,'#skF_9')
      | k1_zfmisc_1('#skF_8') = A_1743 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_72,c_122151])).

tff(c_535,plain,(
    ! [A_110,B_111] :
      ( ~ r2_hidden('#skF_2'(A_110,B_111),A_110)
      | r2_hidden('#skF_3'(A_110,B_111),A_110)
      | B_111 = A_110 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_434,plain,(
    ! [A_97,C_98,B_99] :
      ( m1_subset_1(A_97,C_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(C_98))
      | ~ r2_hidden(A_97,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_444,plain,(
    ! [A_100] :
      ( m1_subset_1(A_100,k1_zfmisc_1('#skF_8'))
      | ~ r2_hidden(A_100,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_137,c_434])).

tff(c_36,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_458,plain,(
    ! [A_100] :
      ( r1_tarski(A_100,'#skF_8')
      | ~ r2_hidden(A_100,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_444,c_36])).

tff(c_552,plain,(
    ! [B_111] :
      ( r1_tarski('#skF_3'('#skF_9',B_111),'#skF_8')
      | ~ r2_hidden('#skF_2'('#skF_9',B_111),'#skF_9')
      | B_111 = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_535,c_458])).

tff(c_122299,plain,
    ( r1_tarski('#skF_3'('#skF_9',k1_zfmisc_1('#skF_8')),'#skF_8')
    | ~ r1_tarski('#skF_9','#skF_9')
    | k1_zfmisc_1('#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_122282,c_552])).

tff(c_122360,plain,
    ( r1_tarski('#skF_3'('#skF_9',k1_zfmisc_1('#skF_8')),'#skF_8')
    | k1_zfmisc_1('#skF_8') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_122299])).

tff(c_122385,plain,(
    k1_zfmisc_1('#skF_8') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_122360])).

tff(c_215,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_1'(A_66,B_67),A_66)
      | r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_226,plain,(
    ! [A_11,B_67] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_11),B_67),A_11)
      | r1_tarski(k1_zfmisc_1(A_11),B_67) ) ),
    inference(resolution,[status(thm)],[c_215,c_22])).

tff(c_333,plain,(
    ! [C_87,B_88,A_89] :
      ( r2_hidden(C_87,B_88)
      | ~ r2_hidden(C_87,A_89)
      | ~ r1_tarski(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2335,plain,(
    ! [A_216,B_217,B_218] :
      ( r2_hidden('#skF_1'(A_216,B_217),B_218)
      | ~ r1_tarski(A_216,B_218)
      | r1_tarski(A_216,B_217) ) ),
    inference(resolution,[status(thm)],[c_6,c_333])).

tff(c_5318,plain,(
    ! [A_334,B_335] :
      ( r1_tarski('#skF_1'(A_334,B_335),'#skF_8')
      | ~ r1_tarski(A_334,'#skF_9')
      | r1_tarski(A_334,B_335) ) ),
    inference(resolution,[status(thm)],[c_2335,c_458])).

tff(c_24,plain,(
    ! [C_15,A_11] :
      ( r2_hidden(C_15,k1_zfmisc_1(A_11))
      | ~ r1_tarski(C_15,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_182,plain,(
    ! [A_61,B_62] :
      ( ~ r2_hidden('#skF_1'(A_61,B_62),B_62)
      | r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_187,plain,(
    ! [A_61,A_11] :
      ( r1_tarski(A_61,k1_zfmisc_1(A_11))
      | ~ r1_tarski('#skF_1'(A_61,k1_zfmisc_1(A_11)),A_11) ) ),
    inference(resolution,[status(thm)],[c_24,c_182])).

tff(c_5387,plain,(
    ! [A_336] :
      ( ~ r1_tarski(A_336,'#skF_9')
      | r1_tarski(A_336,k1_zfmisc_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_5318,c_187])).

tff(c_24766,plain,(
    ! [A_714] :
      ( r1_tarski(A_714,k1_zfmisc_1(k1_zfmisc_1('#skF_8')))
      | ~ r1_tarski('#skF_1'(A_714,k1_zfmisc_1(k1_zfmisc_1('#skF_8'))),'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_5387,c_187])).

tff(c_24884,plain,(
    r1_tarski(k1_zfmisc_1('#skF_9'),k1_zfmisc_1(k1_zfmisc_1('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_226,c_24766])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_25206,plain,
    ( k1_zfmisc_1(k1_zfmisc_1('#skF_8')) = k1_zfmisc_1('#skF_9')
    | ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1('#skF_8')),k1_zfmisc_1('#skF_9')) ),
    inference(resolution,[status(thm)],[c_24884,c_16])).

tff(c_25763,plain,(
    ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1('#skF_8')),k1_zfmisc_1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_25206])).

tff(c_122436,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_9'),k1_zfmisc_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122385,c_25763])).

tff(c_122475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_122436])).

tff(c_122476,plain,(
    r1_tarski('#skF_3'('#skF_9',k1_zfmisc_1('#skF_8')),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_122360])).

tff(c_122477,plain,(
    k1_zfmisc_1('#skF_8') != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_122360])).

tff(c_665,plain,(
    ! [A_124,B_125] :
      ( r2_hidden('#skF_2'(A_124,B_125),B_125)
      | ~ r2_hidden('#skF_3'(A_124,B_125),B_125)
      | B_125 = A_124 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4902,plain,(
    ! [A_311,A_312] :
      ( r2_hidden('#skF_2'(A_311,k1_zfmisc_1(A_312)),k1_zfmisc_1(A_312))
      | k1_zfmisc_1(A_312) = A_311
      | ~ r1_tarski('#skF_3'(A_311,k1_zfmisc_1(A_312)),A_312) ) ),
    inference(resolution,[status(thm)],[c_24,c_665])).

tff(c_4943,plain,(
    ! [A_311,A_312] :
      ( r1_tarski('#skF_2'(A_311,k1_zfmisc_1(A_312)),A_312)
      | k1_zfmisc_1(A_312) = A_311
      | ~ r1_tarski('#skF_3'(A_311,k1_zfmisc_1(A_312)),A_312) ) ),
    inference(resolution,[status(thm)],[c_4902,c_22])).

tff(c_122612,plain,
    ( r1_tarski('#skF_2'('#skF_9',k1_zfmisc_1('#skF_8')),'#skF_8')
    | k1_zfmisc_1('#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_122476,c_4943])).

tff(c_122734,plain,(
    r1_tarski('#skF_2'('#skF_9',k1_zfmisc_1('#skF_8')),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_122477,c_122612])).

tff(c_122915,plain,
    ( r2_hidden('#skF_2'('#skF_9',k1_zfmisc_1('#skF_8')),'#skF_9')
    | ~ v13_waybel_0('#skF_9',k3_yellow_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k1_zfmisc_1('#skF_8'))) ),
    inference(resolution,[status(thm)],[c_122734,c_2766])).

tff(c_123017,plain,(
    r2_hidden('#skF_2'('#skF_9',k1_zfmisc_1('#skF_8')),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_72,c_122915])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7),A_6)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_123117,plain,
    ( ~ r2_hidden('#skF_3'('#skF_9',k1_zfmisc_1('#skF_8')),k1_zfmisc_1('#skF_8'))
    | k1_zfmisc_1('#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_123017,c_8])).

tff(c_123160,plain,(
    ~ r2_hidden('#skF_3'('#skF_9',k1_zfmisc_1('#skF_8')),k1_zfmisc_1('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_122477,c_123117])).

tff(c_123344,plain,(
    ~ r1_tarski('#skF_3'('#skF_9',k1_zfmisc_1('#skF_8')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_24,c_123160])).

tff(c_123388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122476,c_123344])).

tff(c_123389,plain,(
    k1_zfmisc_1(k1_zfmisc_1('#skF_8')) = k1_zfmisc_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_25206])).

tff(c_124621,plain,(
    ! [C_1754] :
      ( r2_hidden(C_1754,k1_zfmisc_1('#skF_9'))
      | ~ r1_tarski(C_1754,k1_zfmisc_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123389,c_24])).

tff(c_124711,plain,(
    ! [C_1755] :
      ( r1_tarski(C_1755,'#skF_9')
      | ~ r1_tarski(C_1755,k1_zfmisc_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_124621,c_22])).

tff(c_124904,plain,(
    r1_tarski(k1_zfmisc_1('#skF_8'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_20,c_124711])).

tff(c_124984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_124904])).

tff(c_124985,plain,(
    k1_zfmisc_1('#skF_8') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_76,plain,(
    v1_subset_1('#skF_9',u1_struct_0(k3_yellow_1('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_127,plain,(
    v1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_76])).

tff(c_124989,plain,(
    v1_subset_1('#skF_9','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124985,c_127])).

tff(c_124992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_124989])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:29:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 40.82/31.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.82/31.42  
% 40.82/31.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.82/31.42  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k3_yellow_1 > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_2 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 40.82/31.42  
% 40.82/31.42  %Foreground sorts:
% 40.82/31.42  
% 40.82/31.42  
% 40.82/31.42  %Background operators:
% 40.82/31.42  
% 40.82/31.42  
% 40.82/31.42  %Foreground operators:
% 40.82/31.42  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 40.82/31.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 40.82/31.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 40.82/31.42  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 40.82/31.42  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 40.82/31.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 40.82/31.42  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 40.82/31.42  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 40.82/31.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 40.82/31.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 40.82/31.42  tff('#skF_10', type, '#skF_10': $i).
% 40.82/31.42  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 40.82/31.42  tff('#skF_9', type, '#skF_9': $i).
% 40.82/31.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 40.82/31.42  tff('#skF_8', type, '#skF_8': $i).
% 40.82/31.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 40.82/31.42  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 40.82/31.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 40.82/31.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 40.82/31.42  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 40.82/31.42  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 40.82/31.42  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 40.82/31.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 40.82/31.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 40.82/31.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 40.82/31.42  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 40.82/31.42  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 40.82/31.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 40.82/31.42  
% 40.82/31.44  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 40.82/31.44  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 40.82/31.44  tff(f_86, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 40.82/31.44  tff(f_73, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 40.82/31.44  tff(f_79, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 40.82/31.44  tff(f_77, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 40.82/31.44  tff(f_121, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 40.82/31.44  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 40.82/31.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 40.82/31.44  tff(f_52, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 40.82/31.44  tff(f_71, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 40.82/31.44  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 40.82/31.44  tff(f_99, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) => (v13_waybel_0(B, k3_yellow_1(A)) <=> (![C, D]: (((r1_tarski(C, D) & r1_tarski(D, A)) & r2_hidden(C, B)) => r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_waybel_7)).
% 40.82/31.44  tff(f_64, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 40.82/31.44  tff(c_20, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 40.82/31.44  tff(c_164, plain, (![A_56, B_57]: (m1_subset_1(A_56, k1_zfmisc_1(B_57)) | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_58])).
% 40.82/31.44  tff(c_54, plain, (![B_29]: (~v1_subset_1(B_29, B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(B_29)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 40.82/31.44  tff(c_168, plain, (![B_57]: (~v1_subset_1(B_57, B_57) | ~r1_tarski(B_57, B_57))), inference(resolution, [status(thm)], [c_164, c_54])).
% 40.82/31.44  tff(c_174, plain, (![B_57]: (~v1_subset_1(B_57, B_57))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_168])).
% 40.82/31.44  tff(c_44, plain, (![A_25]: (k9_setfam_1(A_25)=k1_zfmisc_1(A_25))), inference(cnfTransformation, [status(thm)], [f_73])).
% 40.82/31.44  tff(c_50, plain, (![A_27]: (k2_yellow_1(k9_setfam_1(A_27))=k3_yellow_1(A_27))), inference(cnfTransformation, [status(thm)], [f_79])).
% 40.82/31.44  tff(c_103, plain, (![A_46]: (k2_yellow_1(k1_zfmisc_1(A_46))=k3_yellow_1(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_50])).
% 40.82/31.44  tff(c_46, plain, (![A_26]: (u1_struct_0(k2_yellow_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_77])).
% 40.82/31.44  tff(c_109, plain, (![A_46]: (u1_struct_0(k3_yellow_1(A_46))=k1_zfmisc_1(A_46))), inference(superposition, [status(thm), theory('equality')], [c_103, c_46])).
% 40.82/31.44  tff(c_70, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(u1_struct_0(k3_yellow_1('#skF_8'))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 40.82/31.44  tff(c_137, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k1_zfmisc_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_70])).
% 40.82/31.44  tff(c_147, plain, (![A_50, B_51]: (r1_tarski(A_50, B_51) | ~m1_subset_1(A_50, k1_zfmisc_1(B_51)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 40.82/31.44  tff(c_154, plain, (r1_tarski('#skF_9', k1_zfmisc_1('#skF_8'))), inference(resolution, [status(thm)], [c_137, c_147])).
% 40.82/31.44  tff(c_188, plain, (![B_63, A_64]: (B_63=A_64 | ~r1_tarski(B_63, A_64) | ~r1_tarski(A_64, B_63))), inference(cnfTransformation, [status(thm)], [f_45])).
% 40.82/31.44  tff(c_195, plain, (k1_zfmisc_1('#skF_8')='#skF_9' | ~r1_tarski(k1_zfmisc_1('#skF_8'), '#skF_9')), inference(resolution, [status(thm)], [c_154, c_188])).
% 40.82/31.44  tff(c_214, plain, (~r1_tarski(k1_zfmisc_1('#skF_8'), '#skF_9')), inference(splitLeft, [status(thm)], [c_195])).
% 40.82/31.44  tff(c_72, plain, (v13_waybel_0('#skF_9', k3_yellow_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 40.82/31.44  tff(c_982, plain, (![A_143, B_144]: (r2_hidden('#skF_2'(A_143, B_144), B_144) | r2_hidden('#skF_3'(A_143, B_144), A_143) | B_144=A_143)), inference(cnfTransformation, [status(thm)], [f_39])).
% 40.82/31.44  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 40.82/31.44  tff(c_3536, plain, (![A_269, B_270, B_271]: (r2_hidden('#skF_3'(A_269, B_270), B_271) | ~r1_tarski(A_269, B_271) | r2_hidden('#skF_2'(A_269, B_270), B_270) | B_270=A_269)), inference(resolution, [status(thm)], [c_982, c_2])).
% 40.82/31.44  tff(c_37298, plain, (![A_863, B_864, B_865, B_866]: (r2_hidden('#skF_3'(A_863, B_864), B_865) | ~r1_tarski(B_866, B_865) | ~r1_tarski(A_863, B_866) | r2_hidden('#skF_2'(A_863, B_864), B_864) | B_864=A_863)), inference(resolution, [status(thm)], [c_3536, c_2])).
% 40.82/31.44  tff(c_114640, plain, (![A_1689, B_1690]: (r2_hidden('#skF_3'(A_1689, B_1690), k1_zfmisc_1('#skF_8')) | ~r1_tarski(A_1689, '#skF_9') | r2_hidden('#skF_2'(A_1689, B_1690), B_1690) | B_1690=A_1689)), inference(resolution, [status(thm)], [c_154, c_37298])).
% 40.82/31.44  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 40.82/31.44  tff(c_121909, plain, (![A_1741]: (~r1_tarski(A_1741, '#skF_9') | r2_hidden('#skF_2'(A_1741, k1_zfmisc_1('#skF_8')), k1_zfmisc_1('#skF_8')) | k1_zfmisc_1('#skF_8')=A_1741)), inference(resolution, [status(thm)], [c_114640, c_10])).
% 40.82/31.44  tff(c_22, plain, (![C_15, A_11]: (r1_tarski(C_15, A_11) | ~r2_hidden(C_15, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 40.82/31.44  tff(c_121995, plain, (![A_1742]: (r1_tarski('#skF_2'(A_1742, k1_zfmisc_1('#skF_8')), '#skF_8') | ~r1_tarski(A_1742, '#skF_9') | k1_zfmisc_1('#skF_8')=A_1742)), inference(resolution, [status(thm)], [c_121909, c_22])).
% 40.82/31.44  tff(c_66, plain, (v1_xboole_0('#skF_10')), inference(cnfTransformation, [status(thm)], [f_121])).
% 40.82/31.44  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 40.82/31.44  tff(c_38, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 40.82/31.44  tff(c_257, plain, (![C_73, B_74, A_75]: (~v1_xboole_0(C_73) | ~m1_subset_1(B_74, k1_zfmisc_1(C_73)) | ~r2_hidden(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_71])).
% 40.82/31.44  tff(c_276, plain, (![B_77, A_78, A_79]: (~v1_xboole_0(B_77) | ~r2_hidden(A_78, A_79) | ~r1_tarski(A_79, B_77))), inference(resolution, [status(thm)], [c_38, c_257])).
% 40.82/31.44  tff(c_296, plain, (![B_81, A_82, B_83]: (~v1_xboole_0(B_81) | ~r1_tarski(A_82, B_81) | r1_tarski(A_82, B_83))), inference(resolution, [status(thm)], [c_6, c_276])).
% 40.82/31.44  tff(c_307, plain, (![B_84, B_85]: (~v1_xboole_0(B_84) | r1_tarski(B_84, B_85))), inference(resolution, [status(thm)], [c_20, c_296])).
% 40.82/31.44  tff(c_34, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 40.82/31.44  tff(c_155, plain, (![A_16]: (r1_tarski(k1_xboole_0, A_16))), inference(resolution, [status(thm)], [c_34, c_147])).
% 40.82/31.44  tff(c_196, plain, (![A_16]: (k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_xboole_0))), inference(resolution, [status(thm)], [c_155, c_188])).
% 40.82/31.44  tff(c_328, plain, (![B_86]: (k1_xboole_0=B_86 | ~v1_xboole_0(B_86))), inference(resolution, [status(thm)], [c_307, c_196])).
% 40.82/31.44  tff(c_332, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_66, c_328])).
% 40.82/31.44  tff(c_347, plain, (![A_16]: (r1_tarski('#skF_10', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_155])).
% 40.82/31.44  tff(c_68, plain, (r2_hidden('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_121])).
% 40.82/31.44  tff(c_56, plain, (![D_37, B_31, C_36, A_30]: (r2_hidden(D_37, B_31) | ~r2_hidden(C_36, B_31) | ~r1_tarski(D_37, A_30) | ~r1_tarski(C_36, D_37) | ~v13_waybel_0(B_31, k3_yellow_1(A_30)) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_30)))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 40.82/31.44  tff(c_2718, plain, (![D_234, B_235, C_236, A_237]: (r2_hidden(D_234, B_235) | ~r2_hidden(C_236, B_235) | ~r1_tarski(D_234, A_237) | ~r1_tarski(C_236, D_234) | ~v13_waybel_0(B_235, k3_yellow_1(A_237)) | ~m1_subset_1(B_235, k1_zfmisc_1(k1_zfmisc_1(A_237))))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_56])).
% 40.82/31.44  tff(c_2746, plain, (![D_234, A_237]: (r2_hidden(D_234, '#skF_9') | ~r1_tarski(D_234, A_237) | ~r1_tarski('#skF_10', D_234) | ~v13_waybel_0('#skF_9', k3_yellow_1(A_237)) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k1_zfmisc_1(A_237))))), inference(resolution, [status(thm)], [c_68, c_2718])).
% 40.82/31.44  tff(c_2766, plain, (![D_234, A_237]: (r2_hidden(D_234, '#skF_9') | ~r1_tarski(D_234, A_237) | ~v13_waybel_0('#skF_9', k3_yellow_1(A_237)) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k1_zfmisc_1(A_237))))), inference(demodulation, [status(thm), theory('equality')], [c_347, c_2746])).
% 40.82/31.44  tff(c_122151, plain, (![A_1742]: (r2_hidden('#skF_2'(A_1742, k1_zfmisc_1('#skF_8')), '#skF_9') | ~v13_waybel_0('#skF_9', k3_yellow_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k1_zfmisc_1('#skF_8'))) | ~r1_tarski(A_1742, '#skF_9') | k1_zfmisc_1('#skF_8')=A_1742)), inference(resolution, [status(thm)], [c_121995, c_2766])).
% 40.82/31.44  tff(c_122282, plain, (![A_1743]: (r2_hidden('#skF_2'(A_1743, k1_zfmisc_1('#skF_8')), '#skF_9') | ~r1_tarski(A_1743, '#skF_9') | k1_zfmisc_1('#skF_8')=A_1743)), inference(demodulation, [status(thm), theory('equality')], [c_137, c_72, c_122151])).
% 40.82/31.44  tff(c_535, plain, (![A_110, B_111]: (~r2_hidden('#skF_2'(A_110, B_111), A_110) | r2_hidden('#skF_3'(A_110, B_111), A_110) | B_111=A_110)), inference(cnfTransformation, [status(thm)], [f_39])).
% 40.82/31.44  tff(c_434, plain, (![A_97, C_98, B_99]: (m1_subset_1(A_97, C_98) | ~m1_subset_1(B_99, k1_zfmisc_1(C_98)) | ~r2_hidden(A_97, B_99))), inference(cnfTransformation, [status(thm)], [f_64])).
% 40.82/31.44  tff(c_444, plain, (![A_100]: (m1_subset_1(A_100, k1_zfmisc_1('#skF_8')) | ~r2_hidden(A_100, '#skF_9'))), inference(resolution, [status(thm)], [c_137, c_434])).
% 40.82/31.44  tff(c_36, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 40.82/31.44  tff(c_458, plain, (![A_100]: (r1_tarski(A_100, '#skF_8') | ~r2_hidden(A_100, '#skF_9'))), inference(resolution, [status(thm)], [c_444, c_36])).
% 40.82/31.44  tff(c_552, plain, (![B_111]: (r1_tarski('#skF_3'('#skF_9', B_111), '#skF_8') | ~r2_hidden('#skF_2'('#skF_9', B_111), '#skF_9') | B_111='#skF_9')), inference(resolution, [status(thm)], [c_535, c_458])).
% 40.82/31.44  tff(c_122299, plain, (r1_tarski('#skF_3'('#skF_9', k1_zfmisc_1('#skF_8')), '#skF_8') | ~r1_tarski('#skF_9', '#skF_9') | k1_zfmisc_1('#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_122282, c_552])).
% 40.82/31.44  tff(c_122360, plain, (r1_tarski('#skF_3'('#skF_9', k1_zfmisc_1('#skF_8')), '#skF_8') | k1_zfmisc_1('#skF_8')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_122299])).
% 40.82/31.44  tff(c_122385, plain, (k1_zfmisc_1('#skF_8')='#skF_9'), inference(splitLeft, [status(thm)], [c_122360])).
% 40.82/31.44  tff(c_215, plain, (![A_66, B_67]: (r2_hidden('#skF_1'(A_66, B_67), A_66) | r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 40.82/31.44  tff(c_226, plain, (![A_11, B_67]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_11), B_67), A_11) | r1_tarski(k1_zfmisc_1(A_11), B_67))), inference(resolution, [status(thm)], [c_215, c_22])).
% 40.82/31.44  tff(c_333, plain, (![C_87, B_88, A_89]: (r2_hidden(C_87, B_88) | ~r2_hidden(C_87, A_89) | ~r1_tarski(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_32])).
% 40.82/31.44  tff(c_2335, plain, (![A_216, B_217, B_218]: (r2_hidden('#skF_1'(A_216, B_217), B_218) | ~r1_tarski(A_216, B_218) | r1_tarski(A_216, B_217))), inference(resolution, [status(thm)], [c_6, c_333])).
% 40.82/31.44  tff(c_5318, plain, (![A_334, B_335]: (r1_tarski('#skF_1'(A_334, B_335), '#skF_8') | ~r1_tarski(A_334, '#skF_9') | r1_tarski(A_334, B_335))), inference(resolution, [status(thm)], [c_2335, c_458])).
% 40.82/31.44  tff(c_24, plain, (![C_15, A_11]: (r2_hidden(C_15, k1_zfmisc_1(A_11)) | ~r1_tarski(C_15, A_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 40.82/31.44  tff(c_182, plain, (![A_61, B_62]: (~r2_hidden('#skF_1'(A_61, B_62), B_62) | r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_32])).
% 40.82/31.44  tff(c_187, plain, (![A_61, A_11]: (r1_tarski(A_61, k1_zfmisc_1(A_11)) | ~r1_tarski('#skF_1'(A_61, k1_zfmisc_1(A_11)), A_11))), inference(resolution, [status(thm)], [c_24, c_182])).
% 40.82/31.44  tff(c_5387, plain, (![A_336]: (~r1_tarski(A_336, '#skF_9') | r1_tarski(A_336, k1_zfmisc_1('#skF_8')))), inference(resolution, [status(thm)], [c_5318, c_187])).
% 40.82/31.44  tff(c_24766, plain, (![A_714]: (r1_tarski(A_714, k1_zfmisc_1(k1_zfmisc_1('#skF_8'))) | ~r1_tarski('#skF_1'(A_714, k1_zfmisc_1(k1_zfmisc_1('#skF_8'))), '#skF_9'))), inference(resolution, [status(thm)], [c_5387, c_187])).
% 40.82/31.44  tff(c_24884, plain, (r1_tarski(k1_zfmisc_1('#skF_9'), k1_zfmisc_1(k1_zfmisc_1('#skF_8')))), inference(resolution, [status(thm)], [c_226, c_24766])).
% 40.82/31.44  tff(c_16, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 40.82/31.44  tff(c_25206, plain, (k1_zfmisc_1(k1_zfmisc_1('#skF_8'))=k1_zfmisc_1('#skF_9') | ~r1_tarski(k1_zfmisc_1(k1_zfmisc_1('#skF_8')), k1_zfmisc_1('#skF_9'))), inference(resolution, [status(thm)], [c_24884, c_16])).
% 40.82/31.44  tff(c_25763, plain, (~r1_tarski(k1_zfmisc_1(k1_zfmisc_1('#skF_8')), k1_zfmisc_1('#skF_9'))), inference(splitLeft, [status(thm)], [c_25206])).
% 40.82/31.44  tff(c_122436, plain, (~r1_tarski(k1_zfmisc_1('#skF_9'), k1_zfmisc_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_122385, c_25763])).
% 40.82/31.44  tff(c_122475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_122436])).
% 40.82/31.44  tff(c_122476, plain, (r1_tarski('#skF_3'('#skF_9', k1_zfmisc_1('#skF_8')), '#skF_8')), inference(splitRight, [status(thm)], [c_122360])).
% 40.82/31.44  tff(c_122477, plain, (k1_zfmisc_1('#skF_8')!='#skF_9'), inference(splitRight, [status(thm)], [c_122360])).
% 40.82/31.44  tff(c_665, plain, (![A_124, B_125]: (r2_hidden('#skF_2'(A_124, B_125), B_125) | ~r2_hidden('#skF_3'(A_124, B_125), B_125) | B_125=A_124)), inference(cnfTransformation, [status(thm)], [f_39])).
% 40.82/31.44  tff(c_4902, plain, (![A_311, A_312]: (r2_hidden('#skF_2'(A_311, k1_zfmisc_1(A_312)), k1_zfmisc_1(A_312)) | k1_zfmisc_1(A_312)=A_311 | ~r1_tarski('#skF_3'(A_311, k1_zfmisc_1(A_312)), A_312))), inference(resolution, [status(thm)], [c_24, c_665])).
% 40.82/31.44  tff(c_4943, plain, (![A_311, A_312]: (r1_tarski('#skF_2'(A_311, k1_zfmisc_1(A_312)), A_312) | k1_zfmisc_1(A_312)=A_311 | ~r1_tarski('#skF_3'(A_311, k1_zfmisc_1(A_312)), A_312))), inference(resolution, [status(thm)], [c_4902, c_22])).
% 40.82/31.44  tff(c_122612, plain, (r1_tarski('#skF_2'('#skF_9', k1_zfmisc_1('#skF_8')), '#skF_8') | k1_zfmisc_1('#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_122476, c_4943])).
% 40.82/31.44  tff(c_122734, plain, (r1_tarski('#skF_2'('#skF_9', k1_zfmisc_1('#skF_8')), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_122477, c_122612])).
% 40.82/31.44  tff(c_122915, plain, (r2_hidden('#skF_2'('#skF_9', k1_zfmisc_1('#skF_8')), '#skF_9') | ~v13_waybel_0('#skF_9', k3_yellow_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k1_zfmisc_1('#skF_8')))), inference(resolution, [status(thm)], [c_122734, c_2766])).
% 40.82/31.44  tff(c_123017, plain, (r2_hidden('#skF_2'('#skF_9', k1_zfmisc_1('#skF_8')), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_72, c_122915])).
% 40.82/31.44  tff(c_8, plain, (![A_6, B_7]: (~r2_hidden('#skF_2'(A_6, B_7), A_6) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 40.82/31.44  tff(c_123117, plain, (~r2_hidden('#skF_3'('#skF_9', k1_zfmisc_1('#skF_8')), k1_zfmisc_1('#skF_8')) | k1_zfmisc_1('#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_123017, c_8])).
% 40.82/31.44  tff(c_123160, plain, (~r2_hidden('#skF_3'('#skF_9', k1_zfmisc_1('#skF_8')), k1_zfmisc_1('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_122477, c_123117])).
% 40.82/31.44  tff(c_123344, plain, (~r1_tarski('#skF_3'('#skF_9', k1_zfmisc_1('#skF_8')), '#skF_8')), inference(resolution, [status(thm)], [c_24, c_123160])).
% 40.82/31.44  tff(c_123388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122476, c_123344])).
% 40.82/31.44  tff(c_123389, plain, (k1_zfmisc_1(k1_zfmisc_1('#skF_8'))=k1_zfmisc_1('#skF_9')), inference(splitRight, [status(thm)], [c_25206])).
% 40.82/31.44  tff(c_124621, plain, (![C_1754]: (r2_hidden(C_1754, k1_zfmisc_1('#skF_9')) | ~r1_tarski(C_1754, k1_zfmisc_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_123389, c_24])).
% 40.82/31.44  tff(c_124711, plain, (![C_1755]: (r1_tarski(C_1755, '#skF_9') | ~r1_tarski(C_1755, k1_zfmisc_1('#skF_8')))), inference(resolution, [status(thm)], [c_124621, c_22])).
% 40.82/31.44  tff(c_124904, plain, (r1_tarski(k1_zfmisc_1('#skF_8'), '#skF_9')), inference(resolution, [status(thm)], [c_20, c_124711])).
% 40.82/31.44  tff(c_124984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_124904])).
% 40.82/31.44  tff(c_124985, plain, (k1_zfmisc_1('#skF_8')='#skF_9'), inference(splitRight, [status(thm)], [c_195])).
% 40.82/31.44  tff(c_76, plain, (v1_subset_1('#skF_9', u1_struct_0(k3_yellow_1('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 40.82/31.44  tff(c_127, plain, (v1_subset_1('#skF_9', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_76])).
% 40.82/31.44  tff(c_124989, plain, (v1_subset_1('#skF_9', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_124985, c_127])).
% 40.82/31.44  tff(c_124992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_174, c_124989])).
% 40.82/31.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.82/31.44  
% 40.82/31.44  Inference rules
% 40.82/31.44  ----------------------
% 40.82/31.44  #Ref     : 0
% 40.82/31.44  #Sup     : 31187
% 40.82/31.44  #Fact    : 0
% 40.82/31.44  #Define  : 0
% 40.82/31.44  #Split   : 96
% 40.82/31.44  #Chain   : 0
% 40.82/31.44  #Close   : 0
% 40.82/31.44  
% 40.82/31.44  Ordering : KBO
% 40.82/31.44  
% 40.82/31.44  Simplification rules
% 40.82/31.44  ----------------------
% 40.82/31.44  #Subsume      : 15764
% 40.82/31.44  #Demod        : 7945
% 40.82/31.44  #Tautology    : 3533
% 40.82/31.44  #SimpNegUnit  : 1869
% 40.99/31.44  #BackRed      : 661
% 40.99/31.44  
% 40.99/31.44  #Partial instantiations: 0
% 40.99/31.44  #Strategies tried      : 1
% 40.99/31.44  
% 40.99/31.44  Timing (in seconds)
% 40.99/31.44  ----------------------
% 40.99/31.45  Preprocessing        : 0.33
% 40.99/31.45  Parsing              : 0.17
% 40.99/31.45  CNF conversion       : 0.03
% 40.99/31.45  Main loop            : 30.34
% 40.99/31.45  Inferencing          : 3.06
% 40.99/31.45  Reduction            : 7.14
% 40.99/31.45  Demodulation         : 4.66
% 40.99/31.45  BG Simplification    : 0.32
% 40.99/31.45  Subsumption          : 17.73
% 40.99/31.45  Abstraction          : 0.52
% 40.99/31.45  MUC search           : 0.00
% 40.99/31.45  Cooper               : 0.00
% 40.99/31.45  Total                : 30.72
% 40.99/31.45  Index Insertion      : 0.00
% 40.99/31.45  Index Deletion       : 0.00
% 40.99/31.45  Index Matching       : 0.00
% 40.99/31.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
