%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1742+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:20 EST 2020

% Result     : Theorem 17.55s
% Output     : CNFRefutation 17.72s
% Verified   : 
% Statistics : Number of formulae       :  249 (1200 expanded)
%              Number of leaves         :   38 ( 478 expanded)
%              Depth                    :   26
%              Number of atoms          : 1459 (12180 expanded)
%              Number of equality atoms :   13 ( 935 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k3_funct_2 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_9 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_179,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & v2_pre_topc(C)
                  & l1_pre_topc(C) )
               => ( ( u1_struct_0(A) = u1_struct_0(B)
                    & r1_tarski(u1_pre_topc(B),u1_pre_topc(A)) )
                 => ! [D] :
                      ( ( v1_funct_1(D)
                        & v1_funct_2(D,u1_struct_0(A),u1_struct_0(C))
                        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(C)))) )
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(B),u1_struct_0(C))
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(C)))) )
                         => ( r1_funct_2(u1_struct_0(A),u1_struct_0(C),u1_struct_0(B),u1_struct_0(C),D,E)
                           => ! [F] :
                                ( m1_subset_1(F,u1_struct_0(A))
                               => ! [G] :
                                    ( m1_subset_1(G,u1_struct_0(B))
                                   => ( ( F = G
                                        & r1_tmap_1(B,C,E,G) )
                                     => r1_tmap_1(A,C,D,F) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_tmap_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r1_tmap_1(A,B,C,D)
                  <=> ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                       => ~ ( v3_pre_topc(E,B)
                            & r2_hidden(k3_funct_2(u1_struct_0(A),u1_struct_0(B),C,D),E)
                            & ! [F] :
                                ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(A)))
                               => ~ ( v3_pre_topc(F,A)
                                    & r2_hidden(D,F)
                                    & r1_tarski(k7_relset_1(u1_struct_0(A),u1_struct_0(B),C,F),E) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tmap_1)).

tff(f_55,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_123,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(c_36,plain,(
    ~ r1_tmap_1('#skF_3','#skF_5','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_62,plain,(
    u1_struct_0('#skF_3') = u1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_84,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_44])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_78,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_76,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_66,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_64,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_56,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_81,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_82,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_54])).

tff(c_18,plain,(
    ! [A_14,B_70,C_98,D_112] :
      ( r2_hidden(k3_funct_2(u1_struct_0(A_14),u1_struct_0(B_70),C_98,D_112),'#skF_2'(A_14,B_70,C_98,D_112))
      | r1_tmap_1(A_14,B_70,C_98,D_112)
      | ~ m1_subset_1(D_112,u1_struct_0(A_14))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_14),u1_struct_0(B_70))))
      | ~ v1_funct_2(C_98,u1_struct_0(A_14),u1_struct_0(B_70))
      | ~ v1_funct_1(C_98)
      | ~ l1_pre_topc(B_70)
      | ~ v2_pre_topc(B_70)
      | v2_struct_0(B_70)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_18039,plain,(
    ! [D_2868,F_2866,C_2867,B_2865,A_2869] :
      ( r1_funct_2(A_2869,B_2865,C_2867,D_2868,F_2866,F_2866)
      | ~ m1_subset_1(F_2866,k1_zfmisc_1(k2_zfmisc_1(C_2867,D_2868)))
      | ~ v1_funct_2(F_2866,C_2867,D_2868)
      | ~ m1_subset_1(F_2866,k1_zfmisc_1(k2_zfmisc_1(A_2869,B_2865)))
      | ~ v1_funct_2(F_2866,A_2869,B_2865)
      | ~ v1_funct_1(F_2866)
      | v1_xboole_0(D_2868)
      | v1_xboole_0(B_2865) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18041,plain,(
    ! [A_2869,B_2865] :
      ( r1_funct_2(A_2869,B_2865,u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_6')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_2869,B_2865)))
      | ~ v1_funct_2('#skF_6',A_2869,B_2865)
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | v1_xboole_0(B_2865) ) ),
    inference(resolution,[status(thm)],[c_82,c_18039])).

tff(c_18049,plain,(
    ! [A_2869,B_2865] :
      ( r1_funct_2(A_2869,B_2865,u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_6')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_2869,B_2865)))
      | ~ v1_funct_2('#skF_6',A_2869,B_2865)
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | v1_xboole_0(B_2865) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_81,c_18041])).

tff(c_18066,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_18049])).

tff(c_18188,plain,(
    ! [A_2912,B_2913,C_2914,D_2915] :
      ( m1_subset_1('#skF_2'(A_2912,B_2913,C_2914,D_2915),k1_zfmisc_1(u1_struct_0(B_2913)))
      | r1_tmap_1(A_2912,B_2913,C_2914,D_2915)
      | ~ m1_subset_1(D_2915,u1_struct_0(A_2912))
      | ~ m1_subset_1(C_2914,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2912),u1_struct_0(B_2913))))
      | ~ v1_funct_2(C_2914,u1_struct_0(A_2912),u1_struct_0(B_2913))
      | ~ v1_funct_1(C_2914)
      | ~ l1_pre_topc(B_2913)
      | ~ v2_pre_topc(B_2913)
      | v2_struct_0(B_2913)
      | ~ l1_pre_topc(A_2912)
      | ~ v2_pre_topc(A_2912)
      | v2_struct_0(A_2912) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_18197,plain,(
    ! [B_2913,C_2914,D_2915] :
      ( m1_subset_1('#skF_2'('#skF_3',B_2913,C_2914,D_2915),k1_zfmisc_1(u1_struct_0(B_2913)))
      | r1_tmap_1('#skF_3',B_2913,C_2914,D_2915)
      | ~ m1_subset_1(D_2915,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_2914,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_2913))))
      | ~ v1_funct_2(C_2914,u1_struct_0('#skF_3'),u1_struct_0(B_2913))
      | ~ v1_funct_1(C_2914)
      | ~ l1_pre_topc(B_2913)
      | ~ v2_pre_topc(B_2913)
      | v2_struct_0(B_2913)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_18188])).

tff(c_18210,plain,(
    ! [B_2913,C_2914,D_2915] :
      ( m1_subset_1('#skF_2'('#skF_3',B_2913,C_2914,D_2915),k1_zfmisc_1(u1_struct_0(B_2913)))
      | r1_tmap_1('#skF_3',B_2913,C_2914,D_2915)
      | ~ m1_subset_1(D_2915,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_2914,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_2913))))
      | ~ v1_funct_2(C_2914,u1_struct_0('#skF_4'),u1_struct_0(B_2913))
      | ~ v1_funct_1(C_2914)
      | ~ l1_pre_topc(B_2913)
      | ~ v2_pre_topc(B_2913)
      | v2_struct_0(B_2913)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_62,c_62,c_18197])).

tff(c_18382,plain,(
    ! [B_2942,C_2943,D_2944] :
      ( m1_subset_1('#skF_2'('#skF_3',B_2942,C_2943,D_2944),k1_zfmisc_1(u1_struct_0(B_2942)))
      | r1_tmap_1('#skF_3',B_2942,C_2943,D_2944)
      | ~ m1_subset_1(D_2944,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_2943,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_2942))))
      | ~ v1_funct_2(C_2943,u1_struct_0('#skF_4'),u1_struct_0(B_2942))
      | ~ v1_funct_1(C_2943)
      | ~ l1_pre_topc(B_2942)
      | ~ v2_pre_topc(B_2942)
      | v2_struct_0(B_2942) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_18210])).

tff(c_18384,plain,(
    ! [D_2944] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_2944),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2944)
      | ~ m1_subset_1(D_2944,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_82,c_18382])).

tff(c_18394,plain,(
    ! [D_2944] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_2944),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2944)
      | ~ m1_subset_1(D_2944,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_81,c_18384])).

tff(c_18404,plain,(
    ! [D_2945] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_2945),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2945)
      | ~ m1_subset_1(D_2945,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_18394])).

tff(c_34,plain,(
    ! [C_128,B_127,A_126] :
      ( ~ v1_xboole_0(C_128)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(C_128))
      | ~ r2_hidden(A_126,B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_18414,plain,(
    ! [A_126,D_2945] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_126,'#skF_2'('#skF_3','#skF_5','#skF_6',D_2945))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2945)
      | ~ m1_subset_1(D_2945,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_18404,c_34])).

tff(c_18429,plain,(
    ! [A_2946,D_2947] :
      ( ~ r2_hidden(A_2946,'#skF_2'('#skF_3','#skF_5','#skF_6',D_2947))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2947)
      | ~ m1_subset_1(D_2947,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18066,c_18414])).

tff(c_18433,plain,(
    ! [D_112] :
      ( ~ m1_subset_1(D_112,u1_struct_0('#skF_4'))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_112)
      | ~ m1_subset_1(D_112,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_18429])).

tff(c_18440,plain,(
    ! [D_112] :
      ( r1_tmap_1('#skF_3','#skF_5','#skF_6',D_112)
      | ~ m1_subset_1(D_112,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_66,c_64,c_58,c_81,c_62,c_82,c_62,c_62,c_18433])).

tff(c_18443,plain,(
    ! [D_2948] :
      ( r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2948)
      | ~ m1_subset_1(D_2948,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_68,c_18440])).

tff(c_18446,plain,(
    r1_tmap_1('#skF_3','#skF_5','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_84,c_18443])).

tff(c_18450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_18446])).

tff(c_18452,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_18049])).

tff(c_52,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_50,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_46,plain,(
    r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_83,plain,(
    r1_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_46])).

tff(c_18454,plain,(
    ! [C_2953,E_2955,A_2956,F_2952,B_2951,D_2954] :
      ( F_2952 = E_2955
      | ~ r1_funct_2(A_2956,B_2951,C_2953,D_2954,E_2955,F_2952)
      | ~ m1_subset_1(F_2952,k1_zfmisc_1(k2_zfmisc_1(C_2953,D_2954)))
      | ~ v1_funct_2(F_2952,C_2953,D_2954)
      | ~ v1_funct_1(F_2952)
      | ~ m1_subset_1(E_2955,k1_zfmisc_1(k2_zfmisc_1(A_2956,B_2951)))
      | ~ v1_funct_2(E_2955,A_2956,B_2951)
      | ~ v1_funct_1(E_2955)
      | v1_xboole_0(D_2954)
      | v1_xboole_0(B_2951) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18458,plain,
    ( '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_83,c_18454])).

tff(c_18466,plain,
    ( '#skF_7' = '#skF_6'
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_81,c_82,c_52,c_50,c_48,c_18458])).

tff(c_18467,plain,(
    '#skF_7' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_18452,c_18466])).

tff(c_40,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_38,plain,(
    r1_tmap_1('#skF_4','#skF_5','#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_87,plain,(
    r1_tmap_1('#skF_4','#skF_5','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38])).

tff(c_18474,plain,(
    r1_tmap_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18467,c_87])).

tff(c_18528,plain,(
    ! [A_2971,B_2972,C_2973,D_2974] :
      ( v3_pre_topc('#skF_2'(A_2971,B_2972,C_2973,D_2974),B_2972)
      | r1_tmap_1(A_2971,B_2972,C_2973,D_2974)
      | ~ m1_subset_1(D_2974,u1_struct_0(A_2971))
      | ~ m1_subset_1(C_2973,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2971),u1_struct_0(B_2972))))
      | ~ v1_funct_2(C_2973,u1_struct_0(A_2971),u1_struct_0(B_2972))
      | ~ v1_funct_1(C_2973)
      | ~ l1_pre_topc(B_2972)
      | ~ v2_pre_topc(B_2972)
      | v2_struct_0(B_2972)
      | ~ l1_pre_topc(A_2971)
      | ~ v2_pre_topc(A_2971)
      | v2_struct_0(A_2971) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_18535,plain,(
    ! [B_2972,C_2973,D_2974] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_2972,C_2973,D_2974),B_2972)
      | r1_tmap_1('#skF_3',B_2972,C_2973,D_2974)
      | ~ m1_subset_1(D_2974,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_2973,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_2972))))
      | ~ v1_funct_2(C_2973,u1_struct_0('#skF_3'),u1_struct_0(B_2972))
      | ~ v1_funct_1(C_2973)
      | ~ l1_pre_topc(B_2972)
      | ~ v2_pre_topc(B_2972)
      | v2_struct_0(B_2972)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_18528])).

tff(c_18544,plain,(
    ! [B_2972,C_2973,D_2974] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_2972,C_2973,D_2974),B_2972)
      | r1_tmap_1('#skF_3',B_2972,C_2973,D_2974)
      | ~ m1_subset_1(D_2974,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_2973,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_2972))))
      | ~ v1_funct_2(C_2973,u1_struct_0('#skF_4'),u1_struct_0(B_2972))
      | ~ v1_funct_1(C_2973)
      | ~ l1_pre_topc(B_2972)
      | ~ v2_pre_topc(B_2972)
      | v2_struct_0(B_2972)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_62,c_62,c_18535])).

tff(c_18607,plain,(
    ! [B_2982,C_2983,D_2984] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_2982,C_2983,D_2984),B_2982)
      | r1_tmap_1('#skF_3',B_2982,C_2983,D_2984)
      | ~ m1_subset_1(D_2984,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_2983,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_2982))))
      | ~ v1_funct_2(C_2983,u1_struct_0('#skF_4'),u1_struct_0(B_2982))
      | ~ v1_funct_1(C_2983)
      | ~ l1_pre_topc(B_2982)
      | ~ v2_pre_topc(B_2982)
      | v2_struct_0(B_2982) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_18544])).

tff(c_18609,plain,(
    ! [D_2984] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_2984),'#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2984)
      | ~ m1_subset_1(D_2984,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_82,c_18607])).

tff(c_18617,plain,(
    ! [D_2984] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_2984),'#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2984)
      | ~ m1_subset_1(D_2984,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_81,c_18609])).

tff(c_18618,plain,(
    ! [D_2984] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_2984),'#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2984)
      | ~ m1_subset_1(D_2984,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_18617])).

tff(c_18549,plain,(
    ! [A_2975,B_2976,C_2977,D_2978] :
      ( m1_subset_1('#skF_2'(A_2975,B_2976,C_2977,D_2978),k1_zfmisc_1(u1_struct_0(B_2976)))
      | r1_tmap_1(A_2975,B_2976,C_2977,D_2978)
      | ~ m1_subset_1(D_2978,u1_struct_0(A_2975))
      | ~ m1_subset_1(C_2977,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2975),u1_struct_0(B_2976))))
      | ~ v1_funct_2(C_2977,u1_struct_0(A_2975),u1_struct_0(B_2976))
      | ~ v1_funct_1(C_2977)
      | ~ l1_pre_topc(B_2976)
      | ~ v2_pre_topc(B_2976)
      | v2_struct_0(B_2976)
      | ~ l1_pre_topc(A_2975)
      | ~ v2_pre_topc(A_2975)
      | v2_struct_0(A_2975) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_18556,plain,(
    ! [B_2976,C_2977,D_2978] :
      ( m1_subset_1('#skF_2'('#skF_3',B_2976,C_2977,D_2978),k1_zfmisc_1(u1_struct_0(B_2976)))
      | r1_tmap_1('#skF_3',B_2976,C_2977,D_2978)
      | ~ m1_subset_1(D_2978,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_2977,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_2976))))
      | ~ v1_funct_2(C_2977,u1_struct_0('#skF_3'),u1_struct_0(B_2976))
      | ~ v1_funct_1(C_2977)
      | ~ l1_pre_topc(B_2976)
      | ~ v2_pre_topc(B_2976)
      | v2_struct_0(B_2976)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_18549])).

tff(c_18565,plain,(
    ! [B_2976,C_2977,D_2978] :
      ( m1_subset_1('#skF_2'('#skF_3',B_2976,C_2977,D_2978),k1_zfmisc_1(u1_struct_0(B_2976)))
      | r1_tmap_1('#skF_3',B_2976,C_2977,D_2978)
      | ~ m1_subset_1(D_2978,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_2977,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_2976))))
      | ~ v1_funct_2(C_2977,u1_struct_0('#skF_4'),u1_struct_0(B_2976))
      | ~ v1_funct_1(C_2977)
      | ~ l1_pre_topc(B_2976)
      | ~ v2_pre_topc(B_2976)
      | v2_struct_0(B_2976)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_62,c_62,c_18556])).

tff(c_18742,plain,(
    ! [B_3024,C_3025,D_3026] :
      ( m1_subset_1('#skF_2'('#skF_3',B_3024,C_3025,D_3026),k1_zfmisc_1(u1_struct_0(B_3024)))
      | r1_tmap_1('#skF_3',B_3024,C_3025,D_3026)
      | ~ m1_subset_1(D_3026,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_3025,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_3024))))
      | ~ v1_funct_2(C_3025,u1_struct_0('#skF_4'),u1_struct_0(B_3024))
      | ~ v1_funct_1(C_3025)
      | ~ l1_pre_topc(B_3024)
      | ~ v2_pre_topc(B_3024)
      | v2_struct_0(B_3024) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_18565])).

tff(c_18744,plain,(
    ! [D_3026] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_3026),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_3026)
      | ~ m1_subset_1(D_3026,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_82,c_18742])).

tff(c_18752,plain,(
    ! [D_3026] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_3026),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_3026)
      | ~ m1_subset_1(D_3026,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_81,c_18744])).

tff(c_18753,plain,(
    ! [D_3026] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_3026),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_3026)
      | ~ m1_subset_1(D_3026,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_18752])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_72,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_70,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_18645,plain,(
    ! [A_2990,B_2991,C_2992,D_2993] :
      ( r2_hidden(k3_funct_2(u1_struct_0(A_2990),u1_struct_0(B_2991),C_2992,D_2993),'#skF_2'(A_2990,B_2991,C_2992,D_2993))
      | r1_tmap_1(A_2990,B_2991,C_2992,D_2993)
      | ~ m1_subset_1(D_2993,u1_struct_0(A_2990))
      | ~ m1_subset_1(C_2992,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2990),u1_struct_0(B_2991))))
      | ~ v1_funct_2(C_2992,u1_struct_0(A_2990),u1_struct_0(B_2991))
      | ~ v1_funct_1(C_2992)
      | ~ l1_pre_topc(B_2991)
      | ~ v2_pre_topc(B_2991)
      | v2_struct_0(B_2991)
      | ~ l1_pre_topc(A_2990)
      | ~ v2_pre_topc(A_2990)
      | v2_struct_0(A_2990) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_18656,plain,(
    ! [B_2991,C_2992,D_2993] :
      ( r2_hidden(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_2991),C_2992,D_2993),'#skF_2'('#skF_3',B_2991,C_2992,D_2993))
      | r1_tmap_1('#skF_3',B_2991,C_2992,D_2993)
      | ~ m1_subset_1(D_2993,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_2992,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_2991))))
      | ~ v1_funct_2(C_2992,u1_struct_0('#skF_3'),u1_struct_0(B_2991))
      | ~ v1_funct_1(C_2992)
      | ~ l1_pre_topc(B_2991)
      | ~ v2_pre_topc(B_2991)
      | v2_struct_0(B_2991)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_18645])).

tff(c_18667,plain,(
    ! [B_2991,C_2992,D_2993] :
      ( r2_hidden(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_2991),C_2992,D_2993),'#skF_2'('#skF_3',B_2991,C_2992,D_2993))
      | r1_tmap_1('#skF_3',B_2991,C_2992,D_2993)
      | ~ m1_subset_1(D_2993,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_2992,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_2991))))
      | ~ v1_funct_2(C_2992,u1_struct_0('#skF_4'),u1_struct_0(B_2991))
      | ~ v1_funct_1(C_2992)
      | ~ l1_pre_topc(B_2991)
      | ~ v2_pre_topc(B_2991)
      | v2_struct_0(B_2991)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_62,c_62,c_62,c_18656])).

tff(c_18955,plain,(
    ! [B_3075,C_3076,D_3077] :
      ( r2_hidden(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_3075),C_3076,D_3077),'#skF_2'('#skF_3',B_3075,C_3076,D_3077))
      | r1_tmap_1('#skF_3',B_3075,C_3076,D_3077)
      | ~ m1_subset_1(D_3077,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_3076,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_3075))))
      | ~ v1_funct_2(C_3076,u1_struct_0('#skF_4'),u1_struct_0(B_3075))
      | ~ v1_funct_1(C_3076)
      | ~ l1_pre_topc(B_3075)
      | ~ v2_pre_topc(B_3075)
      | v2_struct_0(B_3075) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_18667])).

tff(c_28,plain,(
    ! [B_70,E_119,D_112,C_98,A_14] :
      ( v3_pre_topc('#skF_1'(E_119,C_98,B_70,D_112,A_14),A_14)
      | ~ r2_hidden(k3_funct_2(u1_struct_0(A_14),u1_struct_0(B_70),C_98,D_112),E_119)
      | ~ v3_pre_topc(E_119,B_70)
      | ~ m1_subset_1(E_119,k1_zfmisc_1(u1_struct_0(B_70)))
      | ~ r1_tmap_1(A_14,B_70,C_98,D_112)
      | ~ m1_subset_1(D_112,u1_struct_0(A_14))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_14),u1_struct_0(B_70))))
      | ~ v1_funct_2(C_98,u1_struct_0(A_14),u1_struct_0(B_70))
      | ~ v1_funct_1(C_98)
      | ~ l1_pre_topc(B_70)
      | ~ v2_pre_topc(B_70)
      | v2_struct_0(B_70)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_18959,plain,(
    ! [B_3075,C_3076,D_3077] :
      ( v3_pre_topc('#skF_1'('#skF_2'('#skF_3',B_3075,C_3076,D_3077),C_3076,B_3075,D_3077,'#skF_4'),'#skF_4')
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_3075,C_3076,D_3077),B_3075)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_3075,C_3076,D_3077),k1_zfmisc_1(u1_struct_0(B_3075)))
      | ~ r1_tmap_1('#skF_4',B_3075,C_3076,D_3077)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | r1_tmap_1('#skF_3',B_3075,C_3076,D_3077)
      | ~ m1_subset_1(D_3077,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_3076,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_3075))))
      | ~ v1_funct_2(C_3076,u1_struct_0('#skF_4'),u1_struct_0(B_3075))
      | ~ v1_funct_1(C_3076)
      | ~ l1_pre_topc(B_3075)
      | ~ v2_pre_topc(B_3075)
      | v2_struct_0(B_3075) ) ),
    inference(resolution,[status(thm)],[c_18955,c_28])).

tff(c_18977,plain,(
    ! [B_3075,C_3076,D_3077] :
      ( v3_pre_topc('#skF_1'('#skF_2'('#skF_3',B_3075,C_3076,D_3077),C_3076,B_3075,D_3077,'#skF_4'),'#skF_4')
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_3075,C_3076,D_3077),B_3075)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_3075,C_3076,D_3077),k1_zfmisc_1(u1_struct_0(B_3075)))
      | ~ r1_tmap_1('#skF_4',B_3075,C_3076,D_3077)
      | v2_struct_0('#skF_4')
      | r1_tmap_1('#skF_3',B_3075,C_3076,D_3077)
      | ~ m1_subset_1(D_3077,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_3076,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_3075))))
      | ~ v1_funct_2(C_3076,u1_struct_0('#skF_4'),u1_struct_0(B_3075))
      | ~ v1_funct_1(C_3076)
      | ~ l1_pre_topc(B_3075)
      | ~ v2_pre_topc(B_3075)
      | v2_struct_0(B_3075) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_18959])).

tff(c_23273,plain,(
    ! [B_3698,C_3699,D_3700] :
      ( v3_pre_topc('#skF_1'('#skF_2'('#skF_3',B_3698,C_3699,D_3700),C_3699,B_3698,D_3700,'#skF_4'),'#skF_4')
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_3698,C_3699,D_3700),B_3698)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_3698,C_3699,D_3700),k1_zfmisc_1(u1_struct_0(B_3698)))
      | ~ r1_tmap_1('#skF_4',B_3698,C_3699,D_3700)
      | r1_tmap_1('#skF_3',B_3698,C_3699,D_3700)
      | ~ m1_subset_1(D_3700,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_3699,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_3698))))
      | ~ v1_funct_2(C_3699,u1_struct_0('#skF_4'),u1_struct_0(B_3698))
      | ~ v1_funct_1(C_3699)
      | ~ l1_pre_topc(B_3698)
      | ~ v2_pre_topc(B_3698)
      | v2_struct_0(B_3698) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_18977])).

tff(c_23275,plain,(
    ! [D_3026] :
      ( v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_3026),'#skF_6','#skF_5',D_3026,'#skF_4'),'#skF_4')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_3026),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_3026)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_3026)
      | ~ m1_subset_1(D_3026,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_18753,c_23273])).

tff(c_23283,plain,(
    ! [D_3026] :
      ( v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_3026),'#skF_6','#skF_5',D_3026,'#skF_4'),'#skF_4')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_3026),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_3026)
      | v2_struct_0('#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_3026)
      | ~ m1_subset_1(D_3026,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_81,c_82,c_23275])).

tff(c_23284,plain,(
    ! [D_3026] :
      ( v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_3026),'#skF_6','#skF_5',D_3026,'#skF_4'),'#skF_4')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_3026),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_3026)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_3026)
      | ~ m1_subset_1(D_3026,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_23283])).

tff(c_18668,plain,(
    ! [B_2991,C_2992,D_2993] :
      ( r2_hidden(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_2991),C_2992,D_2993),'#skF_2'('#skF_3',B_2991,C_2992,D_2993))
      | r1_tmap_1('#skF_3',B_2991,C_2992,D_2993)
      | ~ m1_subset_1(D_2993,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_2992,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_2991))))
      | ~ v1_funct_2(C_2992,u1_struct_0('#skF_4'),u1_struct_0(B_2991))
      | ~ v1_funct_1(C_2992)
      | ~ l1_pre_topc(B_2991)
      | ~ v2_pre_topc(B_2991)
      | v2_struct_0(B_2991) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_18667])).

tff(c_19041,plain,(
    ! [C_3100,E_3099,B_3101,A_3103,D_3102] :
      ( m1_subset_1('#skF_1'(E_3099,C_3100,B_3101,D_3102,A_3103),k1_zfmisc_1(u1_struct_0(A_3103)))
      | ~ r2_hidden(k3_funct_2(u1_struct_0(A_3103),u1_struct_0(B_3101),C_3100,D_3102),E_3099)
      | ~ v3_pre_topc(E_3099,B_3101)
      | ~ m1_subset_1(E_3099,k1_zfmisc_1(u1_struct_0(B_3101)))
      | ~ r1_tmap_1(A_3103,B_3101,C_3100,D_3102)
      | ~ m1_subset_1(D_3102,u1_struct_0(A_3103))
      | ~ m1_subset_1(C_3100,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3103),u1_struct_0(B_3101))))
      | ~ v1_funct_2(C_3100,u1_struct_0(A_3103),u1_struct_0(B_3101))
      | ~ v1_funct_1(C_3100)
      | ~ l1_pre_topc(B_3101)
      | ~ v2_pre_topc(B_3101)
      | v2_struct_0(B_3101)
      | ~ l1_pre_topc(A_3103)
      | ~ v2_pre_topc(A_3103)
      | v2_struct_0(A_3103) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_19043,plain,(
    ! [B_2991,C_2992,D_2993] :
      ( m1_subset_1('#skF_1'('#skF_2'('#skF_3',B_2991,C_2992,D_2993),C_2992,B_2991,D_2993,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_2991,C_2992,D_2993),B_2991)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_2991,C_2992,D_2993),k1_zfmisc_1(u1_struct_0(B_2991)))
      | ~ r1_tmap_1('#skF_4',B_2991,C_2992,D_2993)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | r1_tmap_1('#skF_3',B_2991,C_2992,D_2993)
      | ~ m1_subset_1(D_2993,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_2992,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_2991))))
      | ~ v1_funct_2(C_2992,u1_struct_0('#skF_4'),u1_struct_0(B_2991))
      | ~ v1_funct_1(C_2992)
      | ~ l1_pre_topc(B_2991)
      | ~ v2_pre_topc(B_2991)
      | v2_struct_0(B_2991) ) ),
    inference(resolution,[status(thm)],[c_18668,c_19041])).

tff(c_19062,plain,(
    ! [B_2991,C_2992,D_2993] :
      ( m1_subset_1('#skF_1'('#skF_2'('#skF_3',B_2991,C_2992,D_2993),C_2992,B_2991,D_2993,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_2991,C_2992,D_2993),B_2991)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_2991,C_2992,D_2993),k1_zfmisc_1(u1_struct_0(B_2991)))
      | ~ r1_tmap_1('#skF_4',B_2991,C_2992,D_2993)
      | v2_struct_0('#skF_4')
      | r1_tmap_1('#skF_3',B_2991,C_2992,D_2993)
      | ~ m1_subset_1(D_2993,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_2992,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_2991))))
      | ~ v1_funct_2(C_2992,u1_struct_0('#skF_4'),u1_struct_0(B_2991))
      | ~ v1_funct_1(C_2992)
      | ~ l1_pre_topc(B_2991)
      | ~ v2_pre_topc(B_2991)
      | v2_struct_0(B_2991) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_19043])).

tff(c_23736,plain,(
    ! [B_3772,C_3773,D_3774] :
      ( m1_subset_1('#skF_1'('#skF_2'('#skF_3',B_3772,C_3773,D_3774),C_3773,B_3772,D_3774,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_3772,C_3773,D_3774),B_3772)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_3772,C_3773,D_3774),k1_zfmisc_1(u1_struct_0(B_3772)))
      | ~ r1_tmap_1('#skF_4',B_3772,C_3773,D_3774)
      | r1_tmap_1('#skF_3',B_3772,C_3773,D_3774)
      | ~ m1_subset_1(D_3774,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_3773,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_3772))))
      | ~ v1_funct_2(C_3773,u1_struct_0('#skF_4'),u1_struct_0(B_3772))
      | ~ v1_funct_1(C_3773)
      | ~ l1_pre_topc(B_3772)
      | ~ v2_pre_topc(B_3772)
      | v2_struct_0(B_3772) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_19062])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24520,plain,(
    ! [B_3905,C_3906,D_3907] :
      ( r1_tarski('#skF_1'('#skF_2'('#skF_3',B_3905,C_3906,D_3907),C_3906,B_3905,D_3907,'#skF_4'),u1_struct_0('#skF_4'))
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_3905,C_3906,D_3907),B_3905)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_3905,C_3906,D_3907),k1_zfmisc_1(u1_struct_0(B_3905)))
      | ~ r1_tmap_1('#skF_4',B_3905,C_3906,D_3907)
      | r1_tmap_1('#skF_3',B_3905,C_3906,D_3907)
      | ~ m1_subset_1(D_3907,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_3906,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_3905))))
      | ~ v1_funct_2(C_3906,u1_struct_0('#skF_4'),u1_struct_0(B_3905))
      | ~ v1_funct_1(C_3906)
      | ~ l1_pre_topc(B_3905)
      | ~ v2_pre_topc(B_3905)
      | v2_struct_0(B_3905) ) ),
    inference(resolution,[status(thm)],[c_23736,c_12])).

tff(c_24528,plain,(
    ! [D_3907] :
      ( r1_tarski('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_3907),'#skF_6','#skF_5',D_3907,'#skF_4'),u1_struct_0('#skF_4'))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_3907),'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_3907),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_3907)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_3907)
      | ~ m1_subset_1(D_3907,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_82,c_24520])).

tff(c_24538,plain,(
    ! [D_3907] :
      ( r1_tarski('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_3907),'#skF_6','#skF_5',D_3907,'#skF_4'),u1_struct_0('#skF_4'))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_3907),'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_3907),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_3907)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_3907)
      | ~ m1_subset_1(D_3907,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_81,c_24528])).

tff(c_24544,plain,(
    ! [D_3908] :
      ( r1_tarski('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_3908),'#skF_6','#skF_5',D_3908,'#skF_4'),u1_struct_0('#skF_4'))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_3908),'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_3908),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_3908)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_3908)
      | ~ m1_subset_1(D_3908,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_24538])).

tff(c_7844,plain,(
    ! [A_1429,F_1425,C_1426,D_1427,E_1428,B_1424] :
      ( F_1425 = E_1428
      | ~ r1_funct_2(A_1429,B_1424,C_1426,D_1427,E_1428,F_1425)
      | ~ m1_subset_1(F_1425,k1_zfmisc_1(k2_zfmisc_1(C_1426,D_1427)))
      | ~ v1_funct_2(F_1425,C_1426,D_1427)
      | ~ v1_funct_1(F_1425)
      | ~ m1_subset_1(E_1428,k1_zfmisc_1(k2_zfmisc_1(A_1429,B_1424)))
      | ~ v1_funct_2(E_1428,A_1429,B_1424)
      | ~ v1_funct_1(E_1428)
      | v1_xboole_0(D_1427)
      | v1_xboole_0(B_1424) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7846,plain,
    ( '#skF_7' = '#skF_6'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_83,c_7844])).

tff(c_7849,plain,
    ( '#skF_7' = '#skF_6'
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_81,c_82,c_52,c_50,c_48,c_7846])).

tff(c_7850,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_7849])).

tff(c_7959,plain,(
    ! [A_1465,B_1466,C_1467,D_1468] :
      ( m1_subset_1('#skF_2'(A_1465,B_1466,C_1467,D_1468),k1_zfmisc_1(u1_struct_0(B_1466)))
      | r1_tmap_1(A_1465,B_1466,C_1467,D_1468)
      | ~ m1_subset_1(D_1468,u1_struct_0(A_1465))
      | ~ m1_subset_1(C_1467,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1465),u1_struct_0(B_1466))))
      | ~ v1_funct_2(C_1467,u1_struct_0(A_1465),u1_struct_0(B_1466))
      | ~ v1_funct_1(C_1467)
      | ~ l1_pre_topc(B_1466)
      | ~ v2_pre_topc(B_1466)
      | v2_struct_0(B_1466)
      | ~ l1_pre_topc(A_1465)
      | ~ v2_pre_topc(A_1465)
      | v2_struct_0(A_1465) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_7968,plain,(
    ! [B_1466,C_1467,D_1468] :
      ( m1_subset_1('#skF_2'('#skF_3',B_1466,C_1467,D_1468),k1_zfmisc_1(u1_struct_0(B_1466)))
      | r1_tmap_1('#skF_3',B_1466,C_1467,D_1468)
      | ~ m1_subset_1(D_1468,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_1467,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1466))))
      | ~ v1_funct_2(C_1467,u1_struct_0('#skF_3'),u1_struct_0(B_1466))
      | ~ v1_funct_1(C_1467)
      | ~ l1_pre_topc(B_1466)
      | ~ v2_pre_topc(B_1466)
      | v2_struct_0(B_1466)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_7959])).

tff(c_7981,plain,(
    ! [B_1466,C_1467,D_1468] :
      ( m1_subset_1('#skF_2'('#skF_3',B_1466,C_1467,D_1468),k1_zfmisc_1(u1_struct_0(B_1466)))
      | r1_tmap_1('#skF_3',B_1466,C_1467,D_1468)
      | ~ m1_subset_1(D_1468,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1467,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1466))))
      | ~ v1_funct_2(C_1467,u1_struct_0('#skF_4'),u1_struct_0(B_1466))
      | ~ v1_funct_1(C_1467)
      | ~ l1_pre_topc(B_1466)
      | ~ v2_pre_topc(B_1466)
      | v2_struct_0(B_1466)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_62,c_62,c_7968])).

tff(c_8149,plain,(
    ! [B_1495,C_1496,D_1497] :
      ( m1_subset_1('#skF_2'('#skF_3',B_1495,C_1496,D_1497),k1_zfmisc_1(u1_struct_0(B_1495)))
      | r1_tmap_1('#skF_3',B_1495,C_1496,D_1497)
      | ~ m1_subset_1(D_1497,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1496,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1495))))
      | ~ v1_funct_2(C_1496,u1_struct_0('#skF_4'),u1_struct_0(B_1495))
      | ~ v1_funct_1(C_1496)
      | ~ l1_pre_topc(B_1495)
      | ~ v2_pre_topc(B_1495)
      | v2_struct_0(B_1495) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_7981])).

tff(c_8151,plain,(
    ! [D_1497] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_1497),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1497)
      | ~ m1_subset_1(D_1497,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_82,c_8149])).

tff(c_8161,plain,(
    ! [D_1497] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_1497),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1497)
      | ~ m1_subset_1(D_1497,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_81,c_8151])).

tff(c_8171,plain,(
    ! [D_1498] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_1498),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1498)
      | ~ m1_subset_1(D_1498,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_8161])).

tff(c_8181,plain,(
    ! [A_126,D_1498] :
      ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_126,'#skF_2'('#skF_3','#skF_5','#skF_6',D_1498))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1498)
      | ~ m1_subset_1(D_1498,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_8171,c_34])).

tff(c_8196,plain,(
    ! [A_1499,D_1500] :
      ( ~ r2_hidden(A_1499,'#skF_2'('#skF_3','#skF_5','#skF_6',D_1500))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1500)
      | ~ m1_subset_1(D_1500,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7850,c_8181])).

tff(c_8200,plain,(
    ! [D_112] :
      ( ~ m1_subset_1(D_112,u1_struct_0('#skF_4'))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_112)
      | ~ m1_subset_1(D_112,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_8196])).

tff(c_8207,plain,(
    ! [D_112] :
      ( r1_tmap_1('#skF_3','#skF_5','#skF_6',D_112)
      | ~ m1_subset_1(D_112,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_66,c_64,c_58,c_81,c_62,c_82,c_62,c_62,c_8200])).

tff(c_8210,plain,(
    ! [D_1501] :
      ( r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1501)
      | ~ m1_subset_1(D_1501,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_68,c_8207])).

tff(c_8213,plain,(
    r1_tmap_1('#skF_3','#skF_5','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_84,c_8210])).

tff(c_8217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_8213])).

tff(c_8218,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_7849])).

tff(c_8226,plain,(
    r1_tmap_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8218,c_87])).

tff(c_8237,plain,(
    ! [A_1502,B_1503,C_1504,D_1505] :
      ( v3_pre_topc('#skF_2'(A_1502,B_1503,C_1504,D_1505),B_1503)
      | r1_tmap_1(A_1502,B_1503,C_1504,D_1505)
      | ~ m1_subset_1(D_1505,u1_struct_0(A_1502))
      | ~ m1_subset_1(C_1504,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1502),u1_struct_0(B_1503))))
      | ~ v1_funct_2(C_1504,u1_struct_0(A_1502),u1_struct_0(B_1503))
      | ~ v1_funct_1(C_1504)
      | ~ l1_pre_topc(B_1503)
      | ~ v2_pre_topc(B_1503)
      | v2_struct_0(B_1503)
      | ~ l1_pre_topc(A_1502)
      | ~ v2_pre_topc(A_1502)
      | v2_struct_0(A_1502) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8244,plain,(
    ! [B_1503,C_1504,D_1505] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_1503,C_1504,D_1505),B_1503)
      | r1_tmap_1('#skF_3',B_1503,C_1504,D_1505)
      | ~ m1_subset_1(D_1505,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_1504,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1503))))
      | ~ v1_funct_2(C_1504,u1_struct_0('#skF_3'),u1_struct_0(B_1503))
      | ~ v1_funct_1(C_1504)
      | ~ l1_pre_topc(B_1503)
      | ~ v2_pre_topc(B_1503)
      | v2_struct_0(B_1503)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_8237])).

tff(c_8253,plain,(
    ! [B_1503,C_1504,D_1505] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_1503,C_1504,D_1505),B_1503)
      | r1_tmap_1('#skF_3',B_1503,C_1504,D_1505)
      | ~ m1_subset_1(D_1505,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1504,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1503))))
      | ~ v1_funct_2(C_1504,u1_struct_0('#skF_4'),u1_struct_0(B_1503))
      | ~ v1_funct_1(C_1504)
      | ~ l1_pre_topc(B_1503)
      | ~ v2_pre_topc(B_1503)
      | v2_struct_0(B_1503)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_62,c_62,c_8244])).

tff(c_8480,plain,(
    ! [B_1569,C_1570,D_1571] :
      ( v3_pre_topc('#skF_2'('#skF_3',B_1569,C_1570,D_1571),B_1569)
      | r1_tmap_1('#skF_3',B_1569,C_1570,D_1571)
      | ~ m1_subset_1(D_1571,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1570,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1569))))
      | ~ v1_funct_2(C_1570,u1_struct_0('#skF_4'),u1_struct_0(B_1569))
      | ~ v1_funct_1(C_1570)
      | ~ l1_pre_topc(B_1569)
      | ~ v2_pre_topc(B_1569)
      | v2_struct_0(B_1569) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_8253])).

tff(c_8482,plain,(
    ! [D_1571] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1571),'#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1571)
      | ~ m1_subset_1(D_1571,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_82,c_8480])).

tff(c_8490,plain,(
    ! [D_1571] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1571),'#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1571)
      | ~ m1_subset_1(D_1571,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_81,c_8482])).

tff(c_8491,plain,(
    ! [D_1571] :
      ( v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1571),'#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1571)
      | ~ m1_subset_1(D_1571,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_8490])).

tff(c_8288,plain,(
    ! [A_1519,B_1520,C_1521,D_1522] :
      ( m1_subset_1('#skF_2'(A_1519,B_1520,C_1521,D_1522),k1_zfmisc_1(u1_struct_0(B_1520)))
      | r1_tmap_1(A_1519,B_1520,C_1521,D_1522)
      | ~ m1_subset_1(D_1522,u1_struct_0(A_1519))
      | ~ m1_subset_1(C_1521,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1519),u1_struct_0(B_1520))))
      | ~ v1_funct_2(C_1521,u1_struct_0(A_1519),u1_struct_0(B_1520))
      | ~ v1_funct_1(C_1521)
      | ~ l1_pre_topc(B_1520)
      | ~ v2_pre_topc(B_1520)
      | v2_struct_0(B_1520)
      | ~ l1_pre_topc(A_1519)
      | ~ v2_pre_topc(A_1519)
      | v2_struct_0(A_1519) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8295,plain,(
    ! [B_1520,C_1521,D_1522] :
      ( m1_subset_1('#skF_2'('#skF_3',B_1520,C_1521,D_1522),k1_zfmisc_1(u1_struct_0(B_1520)))
      | r1_tmap_1('#skF_3',B_1520,C_1521,D_1522)
      | ~ m1_subset_1(D_1522,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_1521,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1520))))
      | ~ v1_funct_2(C_1521,u1_struct_0('#skF_3'),u1_struct_0(B_1520))
      | ~ v1_funct_1(C_1521)
      | ~ l1_pre_topc(B_1520)
      | ~ v2_pre_topc(B_1520)
      | v2_struct_0(B_1520)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_8288])).

tff(c_8304,plain,(
    ! [B_1520,C_1521,D_1522] :
      ( m1_subset_1('#skF_2'('#skF_3',B_1520,C_1521,D_1522),k1_zfmisc_1(u1_struct_0(B_1520)))
      | r1_tmap_1('#skF_3',B_1520,C_1521,D_1522)
      | ~ m1_subset_1(D_1522,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1521,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1520))))
      | ~ v1_funct_2(C_1521,u1_struct_0('#skF_4'),u1_struct_0(B_1520))
      | ~ v1_funct_1(C_1521)
      | ~ l1_pre_topc(B_1520)
      | ~ v2_pre_topc(B_1520)
      | v2_struct_0(B_1520)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_62,c_62,c_8295])).

tff(c_8557,plain,(
    ! [B_1591,C_1592,D_1593] :
      ( m1_subset_1('#skF_2'('#skF_3',B_1591,C_1592,D_1593),k1_zfmisc_1(u1_struct_0(B_1591)))
      | r1_tmap_1('#skF_3',B_1591,C_1592,D_1593)
      | ~ m1_subset_1(D_1593,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1592,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1591))))
      | ~ v1_funct_2(C_1592,u1_struct_0('#skF_4'),u1_struct_0(B_1591))
      | ~ v1_funct_1(C_1592)
      | ~ l1_pre_topc(B_1591)
      | ~ v2_pre_topc(B_1591)
      | v2_struct_0(B_1591) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_8304])).

tff(c_8559,plain,(
    ! [D_1593] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1593)
      | ~ m1_subset_1(D_1593,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_82,c_8557])).

tff(c_8567,plain,(
    ! [D_1593] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1593)
      | ~ m1_subset_1(D_1593,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_81,c_8559])).

tff(c_8568,plain,(
    ! [D_1593] :
      ( m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1593)
      | ~ m1_subset_1(D_1593,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_8567])).

tff(c_8387,plain,(
    ! [A_1534,B_1535,C_1536,D_1537] :
      ( r2_hidden(k3_funct_2(u1_struct_0(A_1534),u1_struct_0(B_1535),C_1536,D_1537),'#skF_2'(A_1534,B_1535,C_1536,D_1537))
      | r1_tmap_1(A_1534,B_1535,C_1536,D_1537)
      | ~ m1_subset_1(D_1537,u1_struct_0(A_1534))
      | ~ m1_subset_1(C_1536,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1534),u1_struct_0(B_1535))))
      | ~ v1_funct_2(C_1536,u1_struct_0(A_1534),u1_struct_0(B_1535))
      | ~ v1_funct_1(C_1536)
      | ~ l1_pre_topc(B_1535)
      | ~ v2_pre_topc(B_1535)
      | v2_struct_0(B_1535)
      | ~ l1_pre_topc(A_1534)
      | ~ v2_pre_topc(A_1534)
      | v2_struct_0(A_1534) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8398,plain,(
    ! [B_1535,C_1536,D_1537] :
      ( r2_hidden(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_1535),C_1536,D_1537),'#skF_2'('#skF_3',B_1535,C_1536,D_1537))
      | r1_tmap_1('#skF_3',B_1535,C_1536,D_1537)
      | ~ m1_subset_1(D_1537,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_1536,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_1535))))
      | ~ v1_funct_2(C_1536,u1_struct_0('#skF_3'),u1_struct_0(B_1535))
      | ~ v1_funct_1(C_1536)
      | ~ l1_pre_topc(B_1535)
      | ~ v2_pre_topc(B_1535)
      | v2_struct_0(B_1535)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_8387])).

tff(c_8409,plain,(
    ! [B_1535,C_1536,D_1537] :
      ( r2_hidden(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_1535),C_1536,D_1537),'#skF_2'('#skF_3',B_1535,C_1536,D_1537))
      | r1_tmap_1('#skF_3',B_1535,C_1536,D_1537)
      | ~ m1_subset_1(D_1537,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1536,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1535))))
      | ~ v1_funct_2(C_1536,u1_struct_0('#skF_4'),u1_struct_0(B_1535))
      | ~ v1_funct_1(C_1536)
      | ~ l1_pre_topc(B_1535)
      | ~ v2_pre_topc(B_1535)
      | v2_struct_0(B_1535)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_62,c_62,c_62,c_8398])).

tff(c_8609,plain,(
    ! [B_1596,C_1597,D_1598] :
      ( r2_hidden(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_1596),C_1597,D_1598),'#skF_2'('#skF_3',B_1596,C_1597,D_1598))
      | r1_tmap_1('#skF_3',B_1596,C_1597,D_1598)
      | ~ m1_subset_1(D_1598,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1597,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1596))))
      | ~ v1_funct_2(C_1597,u1_struct_0('#skF_4'),u1_struct_0(B_1596))
      | ~ v1_funct_1(C_1597)
      | ~ l1_pre_topc(B_1596)
      | ~ v2_pre_topc(B_1596)
      | v2_struct_0(B_1596) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_8409])).

tff(c_8611,plain,(
    ! [B_1596,C_1597,D_1598] :
      ( v3_pre_topc('#skF_1'('#skF_2'('#skF_3',B_1596,C_1597,D_1598),C_1597,B_1596,D_1598,'#skF_4'),'#skF_4')
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_1596,C_1597,D_1598),B_1596)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_1596,C_1597,D_1598),k1_zfmisc_1(u1_struct_0(B_1596)))
      | ~ r1_tmap_1('#skF_4',B_1596,C_1597,D_1598)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | r1_tmap_1('#skF_3',B_1596,C_1597,D_1598)
      | ~ m1_subset_1(D_1598,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1597,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1596))))
      | ~ v1_funct_2(C_1597,u1_struct_0('#skF_4'),u1_struct_0(B_1596))
      | ~ v1_funct_1(C_1597)
      | ~ l1_pre_topc(B_1596)
      | ~ v2_pre_topc(B_1596)
      | v2_struct_0(B_1596) ) ),
    inference(resolution,[status(thm)],[c_8609,c_28])).

tff(c_8621,plain,(
    ! [B_1596,C_1597,D_1598] :
      ( v3_pre_topc('#skF_1'('#skF_2'('#skF_3',B_1596,C_1597,D_1598),C_1597,B_1596,D_1598,'#skF_4'),'#skF_4')
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_1596,C_1597,D_1598),B_1596)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_1596,C_1597,D_1598),k1_zfmisc_1(u1_struct_0(B_1596)))
      | ~ r1_tmap_1('#skF_4',B_1596,C_1597,D_1598)
      | v2_struct_0('#skF_4')
      | r1_tmap_1('#skF_3',B_1596,C_1597,D_1598)
      | ~ m1_subset_1(D_1598,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1597,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1596))))
      | ~ v1_funct_2(C_1597,u1_struct_0('#skF_4'),u1_struct_0(B_1596))
      | ~ v1_funct_1(C_1597)
      | ~ l1_pre_topc(B_1596)
      | ~ v2_pre_topc(B_1596)
      | v2_struct_0(B_1596) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_8611])).

tff(c_14652,plain,(
    ! [B_2375,C_2376,D_2377] :
      ( v3_pre_topc('#skF_1'('#skF_2'('#skF_3',B_2375,C_2376,D_2377),C_2376,B_2375,D_2377,'#skF_4'),'#skF_4')
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_2375,C_2376,D_2377),B_2375)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_2375,C_2376,D_2377),k1_zfmisc_1(u1_struct_0(B_2375)))
      | ~ r1_tmap_1('#skF_4',B_2375,C_2376,D_2377)
      | r1_tmap_1('#skF_3',B_2375,C_2376,D_2377)
      | ~ m1_subset_1(D_2377,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_2376,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_2375))))
      | ~ v1_funct_2(C_2376,u1_struct_0('#skF_4'),u1_struct_0(B_2375))
      | ~ v1_funct_1(C_2376)
      | ~ l1_pre_topc(B_2375)
      | ~ v2_pre_topc(B_2375)
      | v2_struct_0(B_2375) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_8621])).

tff(c_14654,plain,(
    ! [D_1593] :
      ( v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_6','#skF_5',D_1593,'#skF_4'),'#skF_4')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_1593)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1593)
      | ~ m1_subset_1(D_1593,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_8568,c_14652])).

tff(c_14662,plain,(
    ! [D_1593] :
      ( v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_6','#skF_5',D_1593,'#skF_4'),'#skF_4')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_1593)
      | v2_struct_0('#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1593)
      | ~ m1_subset_1(D_1593,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_81,c_82,c_14654])).

tff(c_14663,plain,(
    ! [D_1593] :
      ( v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_6','#skF_5',D_1593,'#skF_4'),'#skF_4')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_1593)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1593)
      | ~ m1_subset_1(D_1593,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_14662])).

tff(c_8410,plain,(
    ! [B_1535,C_1536,D_1537] :
      ( r2_hidden(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_1535),C_1536,D_1537),'#skF_2'('#skF_3',B_1535,C_1536,D_1537))
      | r1_tmap_1('#skF_3',B_1535,C_1536,D_1537)
      | ~ m1_subset_1(D_1537,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1536,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1535))))
      | ~ v1_funct_2(C_1536,u1_struct_0('#skF_4'),u1_struct_0(B_1535))
      | ~ v1_funct_1(C_1536)
      | ~ l1_pre_topc(B_1535)
      | ~ v2_pre_topc(B_1535)
      | v2_struct_0(B_1535) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_8409])).

tff(c_8768,plain,(
    ! [C_1635,D_1637,E_1634,B_1636,A_1638] :
      ( m1_subset_1('#skF_1'(E_1634,C_1635,B_1636,D_1637,A_1638),k1_zfmisc_1(u1_struct_0(A_1638)))
      | ~ r2_hidden(k3_funct_2(u1_struct_0(A_1638),u1_struct_0(B_1636),C_1635,D_1637),E_1634)
      | ~ v3_pre_topc(E_1634,B_1636)
      | ~ m1_subset_1(E_1634,k1_zfmisc_1(u1_struct_0(B_1636)))
      | ~ r1_tmap_1(A_1638,B_1636,C_1635,D_1637)
      | ~ m1_subset_1(D_1637,u1_struct_0(A_1638))
      | ~ m1_subset_1(C_1635,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1638),u1_struct_0(B_1636))))
      | ~ v1_funct_2(C_1635,u1_struct_0(A_1638),u1_struct_0(B_1636))
      | ~ v1_funct_1(C_1635)
      | ~ l1_pre_topc(B_1636)
      | ~ v2_pre_topc(B_1636)
      | v2_struct_0(B_1636)
      | ~ l1_pre_topc(A_1638)
      | ~ v2_pre_topc(A_1638)
      | v2_struct_0(A_1638) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8774,plain,(
    ! [B_1535,C_1536,D_1537] :
      ( m1_subset_1('#skF_1'('#skF_2'('#skF_3',B_1535,C_1536,D_1537),C_1536,B_1535,D_1537,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_1535,C_1536,D_1537),B_1535)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_1535,C_1536,D_1537),k1_zfmisc_1(u1_struct_0(B_1535)))
      | ~ r1_tmap_1('#skF_4',B_1535,C_1536,D_1537)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | r1_tmap_1('#skF_3',B_1535,C_1536,D_1537)
      | ~ m1_subset_1(D_1537,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1536,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1535))))
      | ~ v1_funct_2(C_1536,u1_struct_0('#skF_4'),u1_struct_0(B_1535))
      | ~ v1_funct_1(C_1536)
      | ~ l1_pre_topc(B_1535)
      | ~ v2_pre_topc(B_1535)
      | v2_struct_0(B_1535) ) ),
    inference(resolution,[status(thm)],[c_8410,c_8768])).

tff(c_8800,plain,(
    ! [B_1535,C_1536,D_1537] :
      ( m1_subset_1('#skF_1'('#skF_2'('#skF_3',B_1535,C_1536,D_1537),C_1536,B_1535,D_1537,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_1535,C_1536,D_1537),B_1535)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_1535,C_1536,D_1537),k1_zfmisc_1(u1_struct_0(B_1535)))
      | ~ r1_tmap_1('#skF_4',B_1535,C_1536,D_1537)
      | v2_struct_0('#skF_4')
      | r1_tmap_1('#skF_3',B_1535,C_1536,D_1537)
      | ~ m1_subset_1(D_1537,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1536,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1535))))
      | ~ v1_funct_2(C_1536,u1_struct_0('#skF_4'),u1_struct_0(B_1535))
      | ~ v1_funct_1(C_1536)
      | ~ l1_pre_topc(B_1535)
      | ~ v2_pre_topc(B_1535)
      | v2_struct_0(B_1535) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_8774])).

tff(c_15003,plain,(
    ! [B_2426,C_2427,D_2428] :
      ( m1_subset_1('#skF_1'('#skF_2'('#skF_3',B_2426,C_2427,D_2428),C_2427,B_2426,D_2428,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_2426,C_2427,D_2428),B_2426)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_2426,C_2427,D_2428),k1_zfmisc_1(u1_struct_0(B_2426)))
      | ~ r1_tmap_1('#skF_4',B_2426,C_2427,D_2428)
      | r1_tmap_1('#skF_3',B_2426,C_2427,D_2428)
      | ~ m1_subset_1(D_2428,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_2427,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_2426))))
      | ~ v1_funct_2(C_2427,u1_struct_0('#skF_4'),u1_struct_0(B_2426))
      | ~ v1_funct_1(C_2427)
      | ~ l1_pre_topc(B_2426)
      | ~ v2_pre_topc(B_2426)
      | v2_struct_0(B_2426) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_8800])).

tff(c_16165,plain,(
    ! [B_2539,C_2540,D_2541] :
      ( r1_tarski('#skF_1'('#skF_2'('#skF_3',B_2539,C_2540,D_2541),C_2540,B_2539,D_2541,'#skF_4'),u1_struct_0('#skF_4'))
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_2539,C_2540,D_2541),B_2539)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_2539,C_2540,D_2541),k1_zfmisc_1(u1_struct_0(B_2539)))
      | ~ r1_tmap_1('#skF_4',B_2539,C_2540,D_2541)
      | r1_tmap_1('#skF_3',B_2539,C_2540,D_2541)
      | ~ m1_subset_1(D_2541,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_2540,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_2539))))
      | ~ v1_funct_2(C_2540,u1_struct_0('#skF_4'),u1_struct_0(B_2539))
      | ~ v1_funct_1(C_2540)
      | ~ l1_pre_topc(B_2539)
      | ~ v2_pre_topc(B_2539)
      | v2_struct_0(B_2539) ) ),
    inference(resolution,[status(thm)],[c_15003,c_12])).

tff(c_16173,plain,(
    ! [D_2541] :
      ( r1_tarski('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_2541),'#skF_6','#skF_5',D_2541,'#skF_4'),u1_struct_0('#skF_4'))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_2541),'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_2541),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_2541)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2541)
      | ~ m1_subset_1(D_2541,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_82,c_16165])).

tff(c_16183,plain,(
    ! [D_2541] :
      ( r1_tarski('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_2541),'#skF_6','#skF_5',D_2541,'#skF_4'),u1_struct_0('#skF_4'))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_2541),'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_2541),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_2541)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2541)
      | ~ m1_subset_1(D_2541,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_81,c_16173])).

tff(c_16189,plain,(
    ! [D_2542] :
      ( r1_tarski('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_2542),'#skF_6','#skF_5',D_2542,'#skF_4'),u1_struct_0('#skF_4'))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_2542),'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_2542),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_2542)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2542)
      | ~ m1_subset_1(D_2542,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_16183])).

tff(c_60,plain,(
    r1_tarski(u1_pre_topc('#skF_4'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_199,plain,(
    ! [B_282,A_283] :
      ( r2_hidden(B_282,u1_pre_topc(A_283))
      | ~ v3_pre_topc(B_282,A_283)
      | ~ m1_subset_1(B_282,k1_zfmisc_1(u1_struct_0(A_283)))
      | ~ l1_pre_topc(A_283) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_248,plain,(
    ! [A_291,A_292] :
      ( r2_hidden(A_291,u1_pre_topc(A_292))
      | ~ v3_pre_topc(A_291,A_292)
      | ~ l1_pre_topc(A_292)
      | ~ r1_tarski(A_291,u1_struct_0(A_292)) ) ),
    inference(resolution,[status(thm)],[c_14,c_199])).

tff(c_127,plain,(
    ! [A_261,C_262,B_263] :
      ( m1_subset_1(A_261,C_262)
      | ~ m1_subset_1(B_263,k1_zfmisc_1(C_262))
      | ~ r2_hidden(A_261,B_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_135,plain,(
    ! [A_261,B_13,A_12] :
      ( m1_subset_1(A_261,B_13)
      | ~ r2_hidden(A_261,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_14,c_127])).

tff(c_8281,plain,(
    ! [A_1515,B_1516,A_1517] :
      ( m1_subset_1(A_1515,B_1516)
      | ~ r1_tarski(u1_pre_topc(A_1517),B_1516)
      | ~ v3_pre_topc(A_1515,A_1517)
      | ~ l1_pre_topc(A_1517)
      | ~ r1_tarski(A_1515,u1_struct_0(A_1517)) ) ),
    inference(resolution,[status(thm)],[c_248,c_135])).

tff(c_8283,plain,(
    ! [A_1515] :
      ( m1_subset_1(A_1515,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(A_1515,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_1515,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_60,c_8281])).

tff(c_8286,plain,(
    ! [A_1515] :
      ( m1_subset_1(A_1515,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(A_1515,'#skF_4')
      | ~ r1_tarski(A_1515,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_8283])).

tff(c_16225,plain,(
    ! [D_2542] :
      ( m1_subset_1('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_2542),'#skF_6','#skF_5',D_2542,'#skF_4'),u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_2542),'#skF_6','#skF_5',D_2542,'#skF_4'),'#skF_4')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_2542),'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_2542),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_2542)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2542)
      | ~ m1_subset_1(D_2542,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_16189,c_8286])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_111,plain,(
    ! [C_255,B_256,A_257] :
      ( ~ v1_xboole_0(C_255)
      | ~ m1_subset_1(B_256,k1_zfmisc_1(C_255))
      | ~ r2_hidden(A_257,B_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_121,plain,(
    ! [B_258,A_259,A_260] :
      ( ~ v1_xboole_0(B_258)
      | ~ r2_hidden(A_259,A_260)
      | ~ r1_tarski(A_260,B_258) ) ),
    inference(resolution,[status(thm)],[c_14,c_111])).

tff(c_143,plain,(
    ! [B_269,B_270,A_271] :
      ( ~ v1_xboole_0(B_269)
      | ~ r1_tarski(B_270,B_269)
      | v1_xboole_0(B_270)
      | ~ m1_subset_1(A_271,B_270) ) ),
    inference(resolution,[status(thm)],[c_10,c_121])).

tff(c_152,plain,(
    ! [A_271] :
      ( ~ v1_xboole_0(u1_pre_topc('#skF_3'))
      | v1_xboole_0(u1_pre_topc('#skF_4'))
      | ~ m1_subset_1(A_271,u1_pre_topc('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_60,c_143])).

tff(c_153,plain,(
    ~ v1_xboole_0(u1_pre_topc('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_166,plain,(
    ! [B_275,A_276] :
      ( v3_pre_topc(B_275,A_276)
      | ~ r2_hidden(B_275,u1_pre_topc(A_276))
      | ~ m1_subset_1(B_275,k1_zfmisc_1(u1_struct_0(A_276)))
      | ~ l1_pre_topc(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_173,plain,(
    ! [B_275] :
      ( v3_pre_topc(B_275,'#skF_3')
      | ~ r2_hidden(B_275,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_275,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_166])).

tff(c_177,plain,(
    ! [B_277] :
      ( v3_pre_topc(B_277,'#skF_3')
      | ~ r2_hidden(B_277,u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(B_277,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_173])).

tff(c_183,plain,(
    ! [A_278] :
      ( v3_pre_topc(A_278,'#skF_3')
      | ~ r2_hidden(A_278,u1_pre_topc('#skF_3'))
      | ~ r1_tarski(A_278,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_14,c_177])).

tff(c_187,plain,(
    ! [A_10] :
      ( v3_pre_topc(A_10,'#skF_3')
      | ~ r1_tarski(A_10,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_pre_topc('#skF_3'))
      | ~ m1_subset_1(A_10,u1_pre_topc('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_10,c_183])).

tff(c_190,plain,(
    ! [A_10] :
      ( v3_pre_topc(A_10,'#skF_3')
      | ~ r1_tarski(A_10,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_10,u1_pre_topc('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_187])).

tff(c_16258,plain,(
    ! [D_2547] :
      ( v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_2547),'#skF_6','#skF_5',D_2547,'#skF_4'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_2547),'#skF_6','#skF_5',D_2547,'#skF_4'),u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_2547),'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_2547),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_2547)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2547)
      | ~ m1_subset_1(D_2547,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_16189,c_190])).

tff(c_16268,plain,(
    ! [D_2548] :
      ( v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_2548),'#skF_6','#skF_5',D_2548,'#skF_4'),'#skF_3')
      | ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_2548),'#skF_6','#skF_5',D_2548,'#skF_4'),'#skF_4')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_2548),'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_2548),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_2548)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2548)
      | ~ m1_subset_1(D_2548,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_16225,c_16258])).

tff(c_16274,plain,(
    ! [D_1593] :
      ( v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_6','#skF_5',D_1593,'#skF_4'),'#skF_3')
      | ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_6','#skF_5',D_1593,'#skF_4'),'#skF_4')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_1593)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1593)
      | ~ m1_subset_1(D_1593,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_8568,c_16268])).

tff(c_8801,plain,(
    ! [B_1535,C_1536,D_1537] :
      ( m1_subset_1('#skF_1'('#skF_2'('#skF_3',B_1535,C_1536,D_1537),C_1536,B_1535,D_1537,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_1535,C_1536,D_1537),B_1535)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_1535,C_1536,D_1537),k1_zfmisc_1(u1_struct_0(B_1535)))
      | ~ r1_tmap_1('#skF_4',B_1535,C_1536,D_1537)
      | r1_tmap_1('#skF_3',B_1535,C_1536,D_1537)
      | ~ m1_subset_1(D_1537,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1536,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1535))))
      | ~ v1_funct_2(C_1536,u1_struct_0('#skF_4'),u1_struct_0(B_1535))
      | ~ v1_funct_1(C_1536)
      | ~ l1_pre_topc(B_1535)
      | ~ v2_pre_topc(B_1535)
      | v2_struct_0(B_1535) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_8800])).

tff(c_8665,plain,(
    ! [B_1607,C_1606,D_1608,E_1605,A_1609] :
      ( r2_hidden(D_1608,'#skF_1'(E_1605,C_1606,B_1607,D_1608,A_1609))
      | ~ r2_hidden(k3_funct_2(u1_struct_0(A_1609),u1_struct_0(B_1607),C_1606,D_1608),E_1605)
      | ~ v3_pre_topc(E_1605,B_1607)
      | ~ m1_subset_1(E_1605,k1_zfmisc_1(u1_struct_0(B_1607)))
      | ~ r1_tmap_1(A_1609,B_1607,C_1606,D_1608)
      | ~ m1_subset_1(D_1608,u1_struct_0(A_1609))
      | ~ m1_subset_1(C_1606,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1609),u1_struct_0(B_1607))))
      | ~ v1_funct_2(C_1606,u1_struct_0(A_1609),u1_struct_0(B_1607))
      | ~ v1_funct_1(C_1606)
      | ~ l1_pre_topc(B_1607)
      | ~ v2_pre_topc(B_1607)
      | v2_struct_0(B_1607)
      | ~ l1_pre_topc(A_1609)
      | ~ v2_pre_topc(A_1609)
      | v2_struct_0(A_1609) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8667,plain,(
    ! [D_1537,B_1535,C_1536] :
      ( r2_hidden(D_1537,'#skF_1'('#skF_2'('#skF_3',B_1535,C_1536,D_1537),C_1536,B_1535,D_1537,'#skF_4'))
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_1535,C_1536,D_1537),B_1535)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_1535,C_1536,D_1537),k1_zfmisc_1(u1_struct_0(B_1535)))
      | ~ r1_tmap_1('#skF_4',B_1535,C_1536,D_1537)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | r1_tmap_1('#skF_3',B_1535,C_1536,D_1537)
      | ~ m1_subset_1(D_1537,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1536,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1535))))
      | ~ v1_funct_2(C_1536,u1_struct_0('#skF_4'),u1_struct_0(B_1535))
      | ~ v1_funct_1(C_1536)
      | ~ l1_pre_topc(B_1535)
      | ~ v2_pre_topc(B_1535)
      | v2_struct_0(B_1535) ) ),
    inference(resolution,[status(thm)],[c_8410,c_8665])).

tff(c_8685,plain,(
    ! [D_1537,B_1535,C_1536] :
      ( r2_hidden(D_1537,'#skF_1'('#skF_2'('#skF_3',B_1535,C_1536,D_1537),C_1536,B_1535,D_1537,'#skF_4'))
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_1535,C_1536,D_1537),B_1535)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_1535,C_1536,D_1537),k1_zfmisc_1(u1_struct_0(B_1535)))
      | ~ r1_tmap_1('#skF_4',B_1535,C_1536,D_1537)
      | v2_struct_0('#skF_4')
      | r1_tmap_1('#skF_3',B_1535,C_1536,D_1537)
      | ~ m1_subset_1(D_1537,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1536,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1535))))
      | ~ v1_funct_2(C_1536,u1_struct_0('#skF_4'),u1_struct_0(B_1535))
      | ~ v1_funct_1(C_1536)
      | ~ l1_pre_topc(B_1535)
      | ~ v2_pre_topc(B_1535)
      | v2_struct_0(B_1535) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_8667])).

tff(c_14334,plain,(
    ! [D_2302,B_2303,C_2304] :
      ( r2_hidden(D_2302,'#skF_1'('#skF_2'('#skF_3',B_2303,C_2304,D_2302),C_2304,B_2303,D_2302,'#skF_4'))
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_2303,C_2304,D_2302),B_2303)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_2303,C_2304,D_2302),k1_zfmisc_1(u1_struct_0(B_2303)))
      | ~ r1_tmap_1('#skF_4',B_2303,C_2304,D_2302)
      | r1_tmap_1('#skF_3',B_2303,C_2304,D_2302)
      | ~ m1_subset_1(D_2302,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_2304,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_2303))))
      | ~ v1_funct_2(C_2304,u1_struct_0('#skF_4'),u1_struct_0(B_2303))
      | ~ v1_funct_1(C_2304)
      | ~ l1_pre_topc(B_2303)
      | ~ v2_pre_topc(B_2303)
      | v2_struct_0(B_2303) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_8685])).

tff(c_14336,plain,(
    ! [D_1593] :
      ( r2_hidden(D_1593,'#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_6','#skF_5',D_1593,'#skF_4'))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_1593)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1593)
      | ~ m1_subset_1(D_1593,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_8568,c_14334])).

tff(c_14344,plain,(
    ! [D_1593] :
      ( r2_hidden(D_1593,'#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_6','#skF_5',D_1593,'#skF_4'))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_1593)
      | v2_struct_0('#skF_5')
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1593)
      | ~ m1_subset_1(D_1593,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_81,c_82,c_14336])).

tff(c_14345,plain,(
    ! [D_1593] :
      ( r2_hidden(D_1593,'#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_6','#skF_5',D_1593,'#skF_4'))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_1593)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1593)
      | ~ m1_subset_1(D_1593,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_14344])).

tff(c_24,plain,(
    ! [B_70,E_119,D_112,C_98,A_14] :
      ( r1_tarski(k7_relset_1(u1_struct_0(A_14),u1_struct_0(B_70),C_98,'#skF_1'(E_119,C_98,B_70,D_112,A_14)),E_119)
      | ~ r2_hidden(k3_funct_2(u1_struct_0(A_14),u1_struct_0(B_70),C_98,D_112),E_119)
      | ~ v3_pre_topc(E_119,B_70)
      | ~ m1_subset_1(E_119,k1_zfmisc_1(u1_struct_0(B_70)))
      | ~ r1_tmap_1(A_14,B_70,C_98,D_112)
      | ~ m1_subset_1(D_112,u1_struct_0(A_14))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_14),u1_struct_0(B_70))))
      | ~ v1_funct_2(C_98,u1_struct_0(A_14),u1_struct_0(B_70))
      | ~ v1_funct_1(C_98)
      | ~ l1_pre_topc(B_70)
      | ~ v2_pre_topc(B_70)
      | v2_struct_0(B_70)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8453,plain,(
    ! [C_1560,B_1561,F_1559,A_1563,D_1562] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(A_1563),u1_struct_0(B_1561),C_1560,F_1559),'#skF_2'(A_1563,B_1561,C_1560,D_1562))
      | ~ r2_hidden(D_1562,F_1559)
      | ~ v3_pre_topc(F_1559,A_1563)
      | ~ m1_subset_1(F_1559,k1_zfmisc_1(u1_struct_0(A_1563)))
      | r1_tmap_1(A_1563,B_1561,C_1560,D_1562)
      | ~ m1_subset_1(D_1562,u1_struct_0(A_1563))
      | ~ m1_subset_1(C_1560,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1563),u1_struct_0(B_1561))))
      | ~ v1_funct_2(C_1560,u1_struct_0(A_1563),u1_struct_0(B_1561))
      | ~ v1_funct_1(C_1560)
      | ~ l1_pre_topc(B_1561)
      | ~ v2_pre_topc(B_1561)
      | v2_struct_0(B_1561)
      | ~ l1_pre_topc(A_1563)
      | ~ v2_pre_topc(A_1563)
      | v2_struct_0(A_1563) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_8456,plain,(
    ! [B_1561,C_1560,F_1559,D_1562] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0(B_1561),C_1560,F_1559),'#skF_2'('#skF_3',B_1561,C_1560,D_1562))
      | ~ r2_hidden(D_1562,F_1559)
      | ~ v3_pre_topc(F_1559,'#skF_3')
      | ~ m1_subset_1(F_1559,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r1_tmap_1('#skF_3',B_1561,C_1560,D_1562)
      | ~ m1_subset_1(D_1562,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(C_1560,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_1561))))
      | ~ v1_funct_2(C_1560,u1_struct_0('#skF_3'),u1_struct_0(B_1561))
      | ~ v1_funct_1(C_1560)
      | ~ l1_pre_topc(B_1561)
      | ~ v2_pre_topc(B_1561)
      | v2_struct_0(B_1561)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_8453])).

tff(c_8461,plain,(
    ! [B_1561,C_1560,F_1559,D_1562] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0(B_1561),C_1560,F_1559),'#skF_2'('#skF_3',B_1561,C_1560,D_1562))
      | ~ r2_hidden(D_1562,F_1559)
      | ~ v3_pre_topc(F_1559,'#skF_3')
      | ~ m1_subset_1(F_1559,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1('#skF_3',B_1561,C_1560,D_1562)
      | ~ m1_subset_1(D_1562,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1560,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1561))))
      | ~ v1_funct_2(C_1560,u1_struct_0('#skF_4'),u1_struct_0(B_1561))
      | ~ v1_funct_1(C_1560)
      | ~ l1_pre_topc(B_1561)
      | ~ v2_pre_topc(B_1561)
      | v2_struct_0(B_1561)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_62,c_62,c_62,c_62,c_8456])).

tff(c_9231,plain,(
    ! [B_1695,C_1696,F_1697,D_1698] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0('#skF_4'),u1_struct_0(B_1695),C_1696,F_1697),'#skF_2'('#skF_3',B_1695,C_1696,D_1698))
      | ~ r2_hidden(D_1698,F_1697)
      | ~ v3_pre_topc(F_1697,'#skF_3')
      | ~ m1_subset_1(F_1697,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1('#skF_3',B_1695,C_1696,D_1698)
      | ~ m1_subset_1(D_1698,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1696,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1695))))
      | ~ v1_funct_2(C_1696,u1_struct_0('#skF_4'),u1_struct_0(B_1695))
      | ~ v1_funct_1(C_1696)
      | ~ l1_pre_topc(B_1695)
      | ~ v2_pre_topc(B_1695)
      | v2_struct_0(B_1695) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_8461])).

tff(c_9235,plain,(
    ! [D_1698,B_70,C_98,D_112] :
      ( ~ r2_hidden(D_1698,'#skF_1'('#skF_2'('#skF_3',B_70,C_98,D_1698),C_98,B_70,D_112,'#skF_4'))
      | ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3',B_70,C_98,D_1698),C_98,B_70,D_112,'#skF_4'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2'('#skF_3',B_70,C_98,D_1698),C_98,B_70,D_112,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1('#skF_3',B_70,C_98,D_1698)
      | ~ m1_subset_1(D_1698,u1_struct_0('#skF_4'))
      | ~ r2_hidden(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_70),C_98,D_112),'#skF_2'('#skF_3',B_70,C_98,D_1698))
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_70,C_98,D_1698),B_70)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_70,C_98,D_1698),k1_zfmisc_1(u1_struct_0(B_70)))
      | ~ r1_tmap_1('#skF_4',B_70,C_98,D_112)
      | ~ m1_subset_1(D_112,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_70))))
      | ~ v1_funct_2(C_98,u1_struct_0('#skF_4'),u1_struct_0(B_70))
      | ~ v1_funct_1(C_98)
      | ~ l1_pre_topc(B_70)
      | ~ v2_pre_topc(B_70)
      | v2_struct_0(B_70)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_9231])).

tff(c_9241,plain,(
    ! [D_1698,B_70,C_98,D_112] :
      ( ~ r2_hidden(D_1698,'#skF_1'('#skF_2'('#skF_3',B_70,C_98,D_1698),C_98,B_70,D_112,'#skF_4'))
      | ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3',B_70,C_98,D_1698),C_98,B_70,D_112,'#skF_4'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2'('#skF_3',B_70,C_98,D_1698),C_98,B_70,D_112,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1('#skF_3',B_70,C_98,D_1698)
      | ~ m1_subset_1(D_1698,u1_struct_0('#skF_4'))
      | ~ r2_hidden(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_70),C_98,D_112),'#skF_2'('#skF_3',B_70,C_98,D_1698))
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_70,C_98,D_1698),B_70)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_70,C_98,D_1698),k1_zfmisc_1(u1_struct_0(B_70)))
      | ~ r1_tmap_1('#skF_4',B_70,C_98,D_112)
      | ~ m1_subset_1(D_112,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_70))))
      | ~ v1_funct_2(C_98,u1_struct_0('#skF_4'),u1_struct_0(B_70))
      | ~ v1_funct_1(C_98)
      | ~ l1_pre_topc(B_70)
      | ~ v2_pre_topc(B_70)
      | v2_struct_0(B_70)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_9235])).

tff(c_17827,plain,(
    ! [D_2833,B_2834,C_2835,D_2836] :
      ( ~ r2_hidden(D_2833,'#skF_1'('#skF_2'('#skF_3',B_2834,C_2835,D_2833),C_2835,B_2834,D_2836,'#skF_4'))
      | ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3',B_2834,C_2835,D_2833),C_2835,B_2834,D_2836,'#skF_4'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2'('#skF_3',B_2834,C_2835,D_2833),C_2835,B_2834,D_2836,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_tmap_1('#skF_3',B_2834,C_2835,D_2833)
      | ~ m1_subset_1(D_2833,u1_struct_0('#skF_4'))
      | ~ r2_hidden(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_2834),C_2835,D_2836),'#skF_2'('#skF_3',B_2834,C_2835,D_2833))
      | ~ v3_pre_topc('#skF_2'('#skF_3',B_2834,C_2835,D_2833),B_2834)
      | ~ m1_subset_1('#skF_2'('#skF_3',B_2834,C_2835,D_2833),k1_zfmisc_1(u1_struct_0(B_2834)))
      | ~ r1_tmap_1('#skF_4',B_2834,C_2835,D_2836)
      | ~ m1_subset_1(D_2836,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_2835,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_2834))))
      | ~ v1_funct_2(C_2835,u1_struct_0('#skF_4'),u1_struct_0(B_2834))
      | ~ v1_funct_1(C_2835)
      | ~ l1_pre_topc(B_2834)
      | ~ v2_pre_topc(B_2834)
      | v2_struct_0(B_2834) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_9241])).

tff(c_17829,plain,(
    ! [D_1593] :
      ( ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_6','#skF_5',D_1593,'#skF_4'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_6','#skF_5',D_1593,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_1593),'#skF_2'('#skF_3','#skF_5','#skF_6',D_1593))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_1593)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1593)
      | ~ m1_subset_1(D_1593,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_14345,c_17827])).

tff(c_17841,plain,(
    ! [D_1593] :
      ( ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_6','#skF_5',D_1593,'#skF_4'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_6','#skF_5',D_1593,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_1593),'#skF_2'('#skF_3','#skF_5','#skF_6',D_1593))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1593),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_1593)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1593)
      | ~ m1_subset_1(D_1593,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_81,c_82,c_17829])).

tff(c_17852,plain,(
    ! [D_2837] :
      ( ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_2837),'#skF_6','#skF_5',D_2837,'#skF_4'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_2837),'#skF_6','#skF_5',D_2837,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden(k3_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',D_2837),'#skF_2'('#skF_3','#skF_5','#skF_6',D_2837))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_2837),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_2837),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_2837)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2837)
      | ~ m1_subset_1(D_2837,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_17841])).

tff(c_17856,plain,(
    ! [D_1537] :
      ( ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1537),'#skF_6','#skF_5',D_1537,'#skF_4'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1537),'#skF_6','#skF_5',D_1537,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_1537),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1537),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_1537)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1537)
      | ~ m1_subset_1(D_1537,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8410,c_17852])).

tff(c_17862,plain,(
    ! [D_1537] :
      ( ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1537),'#skF_6','#skF_5',D_1537,'#skF_4'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1537),'#skF_6','#skF_5',D_1537,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_1537),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1537),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_1537)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1537)
      | ~ m1_subset_1(D_1537,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_81,c_82,c_17856])).

tff(c_17865,plain,(
    ! [D_2838] :
      ( ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_2838),'#skF_6','#skF_5',D_2838,'#skF_4'),'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_2838),'#skF_6','#skF_5',D_2838,'#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_2838),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_2838),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_2838)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2838)
      | ~ m1_subset_1(D_2838,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_17862])).

tff(c_17869,plain,(
    ! [D_1537] :
      ( ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1537),'#skF_6','#skF_5',D_1537,'#skF_4'),'#skF_3')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1537),'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_1537),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_1537)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1537)
      | ~ m1_subset_1(D_1537,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_8801,c_17865])).

tff(c_17879,plain,(
    ! [D_1537] :
      ( ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_1537),'#skF_6','#skF_5',D_1537,'#skF_4'),'#skF_3')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_1537),'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_1537),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_1537)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_1537)
      | ~ m1_subset_1(D_1537,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_58,c_81,c_82,c_17869])).

tff(c_17883,plain,(
    ! [D_2839] :
      ( ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_2839),'#skF_6','#skF_5',D_2839,'#skF_4'),'#skF_3')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_2839),'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_2839),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_2839)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2839)
      | ~ m1_subset_1(D_2839,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_17879])).

tff(c_17891,plain,(
    ! [D_2840] :
      ( ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_2840),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_2840),'#skF_6','#skF_5',D_2840,'#skF_4'),'#skF_4')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_2840),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_2840)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2840)
      | ~ m1_subset_1(D_2840,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_16274,c_17883])).

tff(c_17899,plain,(
    ! [D_2841] :
      ( ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_2841),'#skF_6','#skF_5',D_2841,'#skF_4'),'#skF_4')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_2841),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_2841)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2841)
      | ~ m1_subset_1(D_2841,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_8568,c_17891])).

tff(c_17914,plain,(
    ! [D_2842] :
      ( ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_2842),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_2842)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2842)
      | ~ m1_subset_1(D_2842,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_14663,c_17899])).

tff(c_17919,plain,(
    ! [D_2843] :
      ( ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_2843)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_2843)
      | ~ m1_subset_1(D_2843,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_8491,c_17914])).

tff(c_17930,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_5','#skF_6','#skF_8')
    | r1_tmap_1('#skF_3','#skF_5','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_84,c_17919])).

tff(c_17935,plain,(
    r1_tmap_1('#skF_3','#skF_5','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8226,c_17930])).

tff(c_17937,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_17935])).

tff(c_17939,plain,(
    v1_xboole_0(u1_pre_topc('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_17940,plain,(
    ! [B_2844,A_2845] :
      ( r2_hidden(B_2844,u1_pre_topc(A_2845))
      | ~ v3_pre_topc(B_2844,A_2845)
      | ~ m1_subset_1(B_2844,k1_zfmisc_1(u1_struct_0(A_2845)))
      | ~ l1_pre_topc(A_2845) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18006,plain,(
    ! [A_2856,A_2857] :
      ( r2_hidden(A_2856,u1_pre_topc(A_2857))
      | ~ v3_pre_topc(A_2856,A_2857)
      | ~ l1_pre_topc(A_2857)
      | ~ r1_tarski(A_2856,u1_struct_0(A_2857)) ) ),
    inference(resolution,[status(thm)],[c_14,c_17940])).

tff(c_119,plain,(
    ! [B_13,A_257,A_12] :
      ( ~ v1_xboole_0(B_13)
      | ~ r2_hidden(A_257,A_12)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_14,c_111])).

tff(c_18032,plain,(
    ! [B_2861,A_2862,A_2863] :
      ( ~ v1_xboole_0(B_2861)
      | ~ r1_tarski(u1_pre_topc(A_2862),B_2861)
      | ~ v3_pre_topc(A_2863,A_2862)
      | ~ l1_pre_topc(A_2862)
      | ~ r1_tarski(A_2863,u1_struct_0(A_2862)) ) ),
    inference(resolution,[status(thm)],[c_18006,c_119])).

tff(c_18034,plain,(
    ! [A_2863] :
      ( ~ v1_xboole_0(u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(A_2863,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_2863,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_60,c_18032])).

tff(c_18037,plain,(
    ! [A_2863] :
      ( ~ v3_pre_topc(A_2863,'#skF_4')
      | ~ r1_tarski(A_2863,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_17939,c_18034])).

tff(c_24573,plain,(
    ! [D_3909] :
      ( ~ v3_pre_topc('#skF_1'('#skF_2'('#skF_3','#skF_5','#skF_6',D_3909),'#skF_6','#skF_5',D_3909,'#skF_4'),'#skF_4')
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_3909),'#skF_5')
      | ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_3909),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_3909)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_3909)
      | ~ m1_subset_1(D_3909,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_24544,c_18037])).

tff(c_24577,plain,(
    ! [D_3910] :
      ( ~ m1_subset_1('#skF_2'('#skF_3','#skF_5','#skF_6',D_3910),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_3910),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_3910)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_3910)
      | ~ m1_subset_1(D_3910,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_23284,c_24573])).

tff(c_24614,plain,(
    ! [D_3915] :
      ( ~ v3_pre_topc('#skF_2'('#skF_3','#skF_5','#skF_6',D_3915),'#skF_5')
      | ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_3915)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_3915)
      | ~ m1_subset_1(D_3915,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_18753,c_24577])).

tff(c_24619,plain,(
    ! [D_3916] :
      ( ~ r1_tmap_1('#skF_4','#skF_5','#skF_6',D_3916)
      | r1_tmap_1('#skF_3','#skF_5','#skF_6',D_3916)
      | ~ m1_subset_1(D_3916,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_18618,c_24614])).

tff(c_24630,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_5','#skF_6','#skF_8')
    | r1_tmap_1('#skF_3','#skF_5','#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_84,c_24619])).

tff(c_24635,plain,(
    r1_tmap_1('#skF_3','#skF_5','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18474,c_24630])).

tff(c_24637,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_24635])).

%------------------------------------------------------------------------------
