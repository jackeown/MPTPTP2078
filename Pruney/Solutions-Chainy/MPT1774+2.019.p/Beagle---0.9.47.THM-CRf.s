%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:27 EST 2020

% Result     : Theorem 4.36s
% Output     : CNFRefutation 4.36s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 338 expanded)
%              Number of leaves         :   34 ( 147 expanded)
%              Depth                    :   12
%              Number of atoms          :  308 (3109 expanded)
%              Number of equality atoms :    5 ( 133 expanded)
%              Maximal formula depth    :   30 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_247,negated_conjecture,(
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
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,B) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(A))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(A)))) )
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(B)))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(D))
                                 => ! [H] :
                                      ( m1_subset_1(H,u1_struct_0(C))
                                     => ( ( v3_pre_topc(F,B)
                                          & r2_hidden(G,F)
                                          & r1_tarski(F,u1_struct_0(C))
                                          & G = H )
                                       => ( r1_tmap_1(D,A,E,G)
                                        <=> r1_tmap_1(C,A,k3_tmap_1(B,A,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_tmap_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_189,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                     => ( m1_pre_topc(C,D)
                       => ! [F] :
                            ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(D))
                               => ! [H] :
                                    ( m1_subset_1(H,u1_struct_0(C))
                                   => ( ( v3_pre_topc(F,D)
                                        & r2_hidden(G,F)
                                        & r1_tarski(F,u1_struct_0(C))
                                        & G = H )
                                     => ( r1_tmap_1(D,B,E,G)
                                      <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v3_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

tff(f_132,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(C))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( F = G
                                  & m1_pre_topc(D,C)
                                  & r1_tmap_1(C,B,E,F) )
                               => r1_tmap_1(D,B,k3_tmap_1(A,B,C,D,E),G) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_50,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_24,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_34,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_75,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_34])).

tff(c_32,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_81,plain,(
    ! [B_666,A_667] :
      ( l1_pre_topc(B_666)
      | ~ m1_pre_topc(B_666,A_667)
      | ~ l1_pre_topc(A_667) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_90,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_81])).

tff(c_97,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_90])).

tff(c_26,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_133,plain,(
    ! [B_677,A_678] :
      ( r1_tarski(u1_struct_0(B_677),u1_struct_0(A_678))
      | ~ m1_pre_topc(B_677,A_678)
      | ~ l1_pre_topc(A_678) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_266,plain,(
    ! [A_702,A_703,B_704] :
      ( r1_tarski(A_702,u1_struct_0(A_703))
      | ~ r1_tarski(A_702,u1_struct_0(B_704))
      | ~ m1_pre_topc(B_704,A_703)
      | ~ l1_pre_topc(A_703) ) ),
    inference(resolution,[status(thm)],[c_133,c_2])).

tff(c_281,plain,(
    ! [A_703] :
      ( r1_tarski('#skF_6',u1_struct_0(A_703))
      | ~ m1_pre_topc('#skF_3',A_703)
      | ~ l1_pre_topc(A_703) ) ),
    inference(resolution,[status(thm)],[c_26,c_266])).

tff(c_28,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_76,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_72,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_73,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_72])).

tff(c_114,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_66,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_74,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_66])).

tff(c_254,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_74])).

tff(c_62,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_60,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_42,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_435,plain,(
    ! [B_725,F_729,C_728,D_723,E_726,A_724,H_727] :
      ( r1_tmap_1(D_723,B_725,E_726,H_727)
      | ~ r1_tmap_1(C_728,B_725,k3_tmap_1(A_724,B_725,D_723,C_728,E_726),H_727)
      | ~ r1_tarski(F_729,u1_struct_0(C_728))
      | ~ r2_hidden(H_727,F_729)
      | ~ v3_pre_topc(F_729,D_723)
      | ~ m1_subset_1(H_727,u1_struct_0(C_728))
      | ~ m1_subset_1(H_727,u1_struct_0(D_723))
      | ~ m1_subset_1(F_729,k1_zfmisc_1(u1_struct_0(D_723)))
      | ~ m1_pre_topc(C_728,D_723)
      | ~ m1_subset_1(E_726,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_723),u1_struct_0(B_725))))
      | ~ v1_funct_2(E_726,u1_struct_0(D_723),u1_struct_0(B_725))
      | ~ v1_funct_1(E_726)
      | ~ m1_pre_topc(D_723,A_724)
      | v2_struct_0(D_723)
      | ~ m1_pre_topc(C_728,A_724)
      | v2_struct_0(C_728)
      | ~ l1_pre_topc(B_725)
      | ~ v2_pre_topc(B_725)
      | v2_struct_0(B_725)
      | ~ l1_pre_topc(A_724)
      | ~ v2_pre_topc(A_724)
      | v2_struct_0(A_724) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_437,plain,(
    ! [F_729] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ r1_tarski(F_729,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_729)
      | ~ v3_pre_topc(F_729,'#skF_4')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_729,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_114,c_435])).

tff(c_440,plain,(
    ! [F_729] :
      ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
      | ~ r1_tarski(F_729,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_729)
      | ~ v3_pre_topc(F_729,'#skF_4')
      | ~ m1_subset_1(F_729,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_62,c_60,c_50,c_46,c_44,c_42,c_40,c_38,c_75,c_32,c_437])).

tff(c_464,plain,(
    ! [F_732] :
      ( ~ r1_tarski(F_732,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',F_732)
      | ~ v3_pre_topc(F_732,'#skF_4')
      | ~ m1_subset_1(F_732,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_64,c_52,c_48,c_254,c_440])).

tff(c_470,plain,(
    ! [A_733] :
      ( ~ r1_tarski(A_733,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',A_733)
      | ~ v3_pre_topc(A_733,'#skF_4')
      | ~ r1_tarski(A_733,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_6,c_464])).

tff(c_496,plain,
    ( ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_4')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_26,c_470])).

tff(c_515,plain,
    ( ~ v3_pre_topc('#skF_6','#skF_4')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_496])).

tff(c_516,plain,(
    ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_515])).

tff(c_525,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_281,c_516])).

tff(c_538,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_38,c_525])).

tff(c_539,plain,(
    ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_515])).

tff(c_540,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_515])).

tff(c_30,plain,(
    v3_pre_topc('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_257,plain,(
    ! [D_699,C_700,A_701] :
      ( v3_pre_topc(D_699,C_700)
      | ~ m1_subset_1(D_699,k1_zfmisc_1(u1_struct_0(C_700)))
      | ~ v3_pre_topc(D_699,A_701)
      | ~ m1_pre_topc(C_700,A_701)
      | ~ m1_subset_1(D_699,k1_zfmisc_1(u1_struct_0(A_701)))
      | ~ l1_pre_topc(A_701) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_541,plain,(
    ! [A_734,C_735,A_736] :
      ( v3_pre_topc(A_734,C_735)
      | ~ v3_pre_topc(A_734,A_736)
      | ~ m1_pre_topc(C_735,A_736)
      | ~ m1_subset_1(A_734,k1_zfmisc_1(u1_struct_0(A_736)))
      | ~ l1_pre_topc(A_736)
      | ~ r1_tarski(A_734,u1_struct_0(C_735)) ) ),
    inference(resolution,[status(thm)],[c_6,c_257])).

tff(c_549,plain,(
    ! [A_734] :
      ( v3_pre_topc(A_734,'#skF_4')
      | ~ v3_pre_topc(A_734,'#skF_2')
      | ~ m1_subset_1(A_734,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_734,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_46,c_541])).

tff(c_1139,plain,(
    ! [A_779] :
      ( v3_pre_topc(A_779,'#skF_4')
      | ~ v3_pre_topc(A_779,'#skF_2')
      | ~ m1_subset_1(A_779,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_tarski(A_779,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_549])).

tff(c_1146,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_2')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_1139])).

tff(c_1150,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_30,c_1146])).

tff(c_1152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_539,c_1150])).

tff(c_1153,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_1434,plain,(
    ! [G_826,A_823,E_827,C_824,B_825,D_828] :
      ( r1_tmap_1(D_828,B_825,k3_tmap_1(A_823,B_825,C_824,D_828,E_827),G_826)
      | ~ r1_tmap_1(C_824,B_825,E_827,G_826)
      | ~ m1_pre_topc(D_828,C_824)
      | ~ m1_subset_1(G_826,u1_struct_0(D_828))
      | ~ m1_subset_1(G_826,u1_struct_0(C_824))
      | ~ m1_subset_1(E_827,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_824),u1_struct_0(B_825))))
      | ~ v1_funct_2(E_827,u1_struct_0(C_824),u1_struct_0(B_825))
      | ~ v1_funct_1(E_827)
      | ~ m1_pre_topc(D_828,A_823)
      | v2_struct_0(D_828)
      | ~ m1_pre_topc(C_824,A_823)
      | v2_struct_0(C_824)
      | ~ l1_pre_topc(B_825)
      | ~ v2_pre_topc(B_825)
      | v2_struct_0(B_825)
      | ~ l1_pre_topc(A_823)
      | ~ v2_pre_topc(A_823)
      | v2_struct_0(A_823) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1436,plain,(
    ! [D_828,A_823,G_826] :
      ( r1_tmap_1(D_828,'#skF_1',k3_tmap_1(A_823,'#skF_1','#skF_4',D_828,'#skF_5'),G_826)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_826)
      | ~ m1_pre_topc(D_828,'#skF_4')
      | ~ m1_subset_1(G_826,u1_struct_0(D_828))
      | ~ m1_subset_1(G_826,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_828,A_823)
      | v2_struct_0(D_828)
      | ~ m1_pre_topc('#skF_4',A_823)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_823)
      | ~ v2_pre_topc(A_823)
      | v2_struct_0(A_823) ) ),
    inference(resolution,[status(thm)],[c_40,c_1434])).

tff(c_1442,plain,(
    ! [D_828,A_823,G_826] :
      ( r1_tmap_1(D_828,'#skF_1',k3_tmap_1(A_823,'#skF_1','#skF_4',D_828,'#skF_5'),G_826)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_826)
      | ~ m1_pre_topc(D_828,'#skF_4')
      | ~ m1_subset_1(G_826,u1_struct_0(D_828))
      | ~ m1_subset_1(G_826,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_828,A_823)
      | v2_struct_0(D_828)
      | ~ m1_pre_topc('#skF_4',A_823)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_823)
      | ~ v2_pre_topc(A_823)
      | v2_struct_0(A_823) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_44,c_42,c_1436])).

tff(c_1467,plain,(
    ! [D_831,A_832,G_833] :
      ( r1_tmap_1(D_831,'#skF_1',k3_tmap_1(A_832,'#skF_1','#skF_4',D_831,'#skF_5'),G_833)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_833)
      | ~ m1_pre_topc(D_831,'#skF_4')
      | ~ m1_subset_1(G_833,u1_struct_0(D_831))
      | ~ m1_subset_1(G_833,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_831,A_832)
      | v2_struct_0(D_831)
      | ~ m1_pre_topc('#skF_4',A_832)
      | ~ l1_pre_topc(A_832)
      | ~ v2_pre_topc(A_832)
      | v2_struct_0(A_832) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_48,c_1442])).

tff(c_1170,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1153,c_74])).

tff(c_1470,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_8')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1467,c_1170])).

tff(c_1473,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_46,c_50,c_75,c_32,c_38,c_1153,c_1470])).

tff(c_1475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_52,c_1473])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:45:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.36/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.36/1.75  
% 4.36/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.36/1.75  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 4.36/1.75  
% 4.36/1.75  %Foreground sorts:
% 4.36/1.75  
% 4.36/1.75  
% 4.36/1.75  %Background operators:
% 4.36/1.75  
% 4.36/1.75  
% 4.36/1.75  %Foreground operators:
% 4.36/1.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.36/1.75  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.36/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.36/1.75  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.36/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.36/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.36/1.75  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.36/1.75  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.36/1.75  tff('#skF_7', type, '#skF_7': $i).
% 4.36/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.36/1.75  tff('#skF_5', type, '#skF_5': $i).
% 4.36/1.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.36/1.75  tff('#skF_6', type, '#skF_6': $i).
% 4.36/1.75  tff('#skF_2', type, '#skF_2': $i).
% 4.36/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.36/1.75  tff('#skF_1', type, '#skF_1': $i).
% 4.36/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.36/1.75  tff('#skF_8', type, '#skF_8': $i).
% 4.36/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.36/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.36/1.75  tff('#skF_4', type, '#skF_4': $i).
% 4.36/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.36/1.75  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.36/1.75  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.36/1.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.36/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.36/1.75  
% 4.36/1.77  tff(f_247, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(B))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, B) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, A, E, G) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_tmap_1)).
% 4.36/1.77  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.36/1.77  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 4.36/1.77  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.36/1.77  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.36/1.77  tff(f_189, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 4.36/1.77  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_tops_2)).
% 4.36/1.77  tff(f_132, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_tmap_1)).
% 4.36/1.77  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_46, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_50, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_24, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_34, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_75, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_34])).
% 4.36/1.77  tff(c_32, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_81, plain, (![B_666, A_667]: (l1_pre_topc(B_666) | ~m1_pre_topc(B_666, A_667) | ~l1_pre_topc(A_667))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.36/1.77  tff(c_90, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_81])).
% 4.36/1.77  tff(c_97, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_90])).
% 4.36/1.77  tff(c_26, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_133, plain, (![B_677, A_678]: (r1_tarski(u1_struct_0(B_677), u1_struct_0(A_678)) | ~m1_pre_topc(B_677, A_678) | ~l1_pre_topc(A_678))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.36/1.77  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.36/1.77  tff(c_266, plain, (![A_702, A_703, B_704]: (r1_tarski(A_702, u1_struct_0(A_703)) | ~r1_tarski(A_702, u1_struct_0(B_704)) | ~m1_pre_topc(B_704, A_703) | ~l1_pre_topc(A_703))), inference(resolution, [status(thm)], [c_133, c_2])).
% 4.36/1.77  tff(c_281, plain, (![A_703]: (r1_tarski('#skF_6', u1_struct_0(A_703)) | ~m1_pre_topc('#skF_3', A_703) | ~l1_pre_topc(A_703))), inference(resolution, [status(thm)], [c_26, c_266])).
% 4.36/1.77  tff(c_28, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_76, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 4.36/1.77  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.36/1.77  tff(c_64, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_48, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_72, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_73, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_72])).
% 4.36/1.77  tff(c_114, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_73])).
% 4.36/1.77  tff(c_66, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_74, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_66])).
% 4.36/1.77  tff(c_254, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_74])).
% 4.36/1.77  tff(c_62, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_60, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_42, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_435, plain, (![B_725, F_729, C_728, D_723, E_726, A_724, H_727]: (r1_tmap_1(D_723, B_725, E_726, H_727) | ~r1_tmap_1(C_728, B_725, k3_tmap_1(A_724, B_725, D_723, C_728, E_726), H_727) | ~r1_tarski(F_729, u1_struct_0(C_728)) | ~r2_hidden(H_727, F_729) | ~v3_pre_topc(F_729, D_723) | ~m1_subset_1(H_727, u1_struct_0(C_728)) | ~m1_subset_1(H_727, u1_struct_0(D_723)) | ~m1_subset_1(F_729, k1_zfmisc_1(u1_struct_0(D_723))) | ~m1_pre_topc(C_728, D_723) | ~m1_subset_1(E_726, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_723), u1_struct_0(B_725)))) | ~v1_funct_2(E_726, u1_struct_0(D_723), u1_struct_0(B_725)) | ~v1_funct_1(E_726) | ~m1_pre_topc(D_723, A_724) | v2_struct_0(D_723) | ~m1_pre_topc(C_728, A_724) | v2_struct_0(C_728) | ~l1_pre_topc(B_725) | ~v2_pre_topc(B_725) | v2_struct_0(B_725) | ~l1_pre_topc(A_724) | ~v2_pre_topc(A_724) | v2_struct_0(A_724))), inference(cnfTransformation, [status(thm)], [f_189])).
% 4.36/1.77  tff(c_437, plain, (![F_729]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~r1_tarski(F_729, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', F_729) | ~v3_pre_topc(F_729, '#skF_4') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(F_729, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_114, c_435])).
% 4.36/1.77  tff(c_440, plain, (![F_729]: (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~r1_tarski(F_729, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', F_729) | ~v3_pre_topc(F_729, '#skF_4') | ~m1_subset_1(F_729, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_62, c_60, c_50, c_46, c_44, c_42, c_40, c_38, c_75, c_32, c_437])).
% 4.36/1.77  tff(c_464, plain, (![F_732]: (~r1_tarski(F_732, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', F_732) | ~v3_pre_topc(F_732, '#skF_4') | ~m1_subset_1(F_732, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_58, c_64, c_52, c_48, c_254, c_440])).
% 4.36/1.77  tff(c_470, plain, (![A_733]: (~r1_tarski(A_733, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', A_733) | ~v3_pre_topc(A_733, '#skF_4') | ~r1_tarski(A_733, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_6, c_464])).
% 4.36/1.77  tff(c_496, plain, (~r2_hidden('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4') | ~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_470])).
% 4.36/1.77  tff(c_515, plain, (~v3_pre_topc('#skF_6', '#skF_4') | ~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_496])).
% 4.36/1.77  tff(c_516, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_515])).
% 4.36/1.77  tff(c_525, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_281, c_516])).
% 4.36/1.77  tff(c_538, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_38, c_525])).
% 4.36/1.77  tff(c_539, plain, (~v3_pre_topc('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_515])).
% 4.36/1.77  tff(c_540, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_515])).
% 4.36/1.77  tff(c_30, plain, (v3_pre_topc('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_247])).
% 4.36/1.77  tff(c_257, plain, (![D_699, C_700, A_701]: (v3_pre_topc(D_699, C_700) | ~m1_subset_1(D_699, k1_zfmisc_1(u1_struct_0(C_700))) | ~v3_pre_topc(D_699, A_701) | ~m1_pre_topc(C_700, A_701) | ~m1_subset_1(D_699, k1_zfmisc_1(u1_struct_0(A_701))) | ~l1_pre_topc(A_701))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.36/1.77  tff(c_541, plain, (![A_734, C_735, A_736]: (v3_pre_topc(A_734, C_735) | ~v3_pre_topc(A_734, A_736) | ~m1_pre_topc(C_735, A_736) | ~m1_subset_1(A_734, k1_zfmisc_1(u1_struct_0(A_736))) | ~l1_pre_topc(A_736) | ~r1_tarski(A_734, u1_struct_0(C_735)))), inference(resolution, [status(thm)], [c_6, c_257])).
% 4.36/1.77  tff(c_549, plain, (![A_734]: (v3_pre_topc(A_734, '#skF_4') | ~v3_pre_topc(A_734, '#skF_2') | ~m1_subset_1(A_734, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_734, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_46, c_541])).
% 4.36/1.77  tff(c_1139, plain, (![A_779]: (v3_pre_topc(A_779, '#skF_4') | ~v3_pre_topc(A_779, '#skF_2') | ~m1_subset_1(A_779, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski(A_779, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_549])).
% 4.36/1.77  tff(c_1146, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_2') | ~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_1139])).
% 4.36/1.77  tff(c_1150, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_540, c_30, c_1146])).
% 4.36/1.77  tff(c_1152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_539, c_1150])).
% 4.36/1.77  tff(c_1153, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_73])).
% 4.36/1.77  tff(c_1434, plain, (![G_826, A_823, E_827, C_824, B_825, D_828]: (r1_tmap_1(D_828, B_825, k3_tmap_1(A_823, B_825, C_824, D_828, E_827), G_826) | ~r1_tmap_1(C_824, B_825, E_827, G_826) | ~m1_pre_topc(D_828, C_824) | ~m1_subset_1(G_826, u1_struct_0(D_828)) | ~m1_subset_1(G_826, u1_struct_0(C_824)) | ~m1_subset_1(E_827, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_824), u1_struct_0(B_825)))) | ~v1_funct_2(E_827, u1_struct_0(C_824), u1_struct_0(B_825)) | ~v1_funct_1(E_827) | ~m1_pre_topc(D_828, A_823) | v2_struct_0(D_828) | ~m1_pre_topc(C_824, A_823) | v2_struct_0(C_824) | ~l1_pre_topc(B_825) | ~v2_pre_topc(B_825) | v2_struct_0(B_825) | ~l1_pre_topc(A_823) | ~v2_pre_topc(A_823) | v2_struct_0(A_823))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.36/1.77  tff(c_1436, plain, (![D_828, A_823, G_826]: (r1_tmap_1(D_828, '#skF_1', k3_tmap_1(A_823, '#skF_1', '#skF_4', D_828, '#skF_5'), G_826) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_826) | ~m1_pre_topc(D_828, '#skF_4') | ~m1_subset_1(G_826, u1_struct_0(D_828)) | ~m1_subset_1(G_826, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_828, A_823) | v2_struct_0(D_828) | ~m1_pre_topc('#skF_4', A_823) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_823) | ~v2_pre_topc(A_823) | v2_struct_0(A_823))), inference(resolution, [status(thm)], [c_40, c_1434])).
% 4.36/1.77  tff(c_1442, plain, (![D_828, A_823, G_826]: (r1_tmap_1(D_828, '#skF_1', k3_tmap_1(A_823, '#skF_1', '#skF_4', D_828, '#skF_5'), G_826) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_826) | ~m1_pre_topc(D_828, '#skF_4') | ~m1_subset_1(G_826, u1_struct_0(D_828)) | ~m1_subset_1(G_826, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_828, A_823) | v2_struct_0(D_828) | ~m1_pre_topc('#skF_4', A_823) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_823) | ~v2_pre_topc(A_823) | v2_struct_0(A_823))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_44, c_42, c_1436])).
% 4.36/1.77  tff(c_1467, plain, (![D_831, A_832, G_833]: (r1_tmap_1(D_831, '#skF_1', k3_tmap_1(A_832, '#skF_1', '#skF_4', D_831, '#skF_5'), G_833) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_833) | ~m1_pre_topc(D_831, '#skF_4') | ~m1_subset_1(G_833, u1_struct_0(D_831)) | ~m1_subset_1(G_833, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_831, A_832) | v2_struct_0(D_831) | ~m1_pre_topc('#skF_4', A_832) | ~l1_pre_topc(A_832) | ~v2_pre_topc(A_832) | v2_struct_0(A_832))), inference(negUnitSimplification, [status(thm)], [c_64, c_48, c_1442])).
% 4.36/1.77  tff(c_1170, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1153, c_74])).
% 4.36/1.77  tff(c_1470, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_8') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1467, c_1170])).
% 4.36/1.77  tff(c_1473, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_46, c_50, c_75, c_32, c_38, c_1153, c_1470])).
% 4.36/1.77  tff(c_1475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_52, c_1473])).
% 4.36/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.36/1.78  
% 4.36/1.78  Inference rules
% 4.36/1.78  ----------------------
% 4.36/1.78  #Ref     : 0
% 4.36/1.78  #Sup     : 338
% 4.36/1.78  #Fact    : 0
% 4.36/1.78  #Define  : 0
% 4.36/1.78  #Split   : 16
% 4.36/1.78  #Chain   : 0
% 4.36/1.78  #Close   : 0
% 4.36/1.78  
% 4.36/1.78  Ordering : KBO
% 4.36/1.78  
% 4.36/1.78  Simplification rules
% 4.36/1.78  ----------------------
% 4.36/1.78  #Subsume      : 113
% 4.36/1.78  #Demod        : 186
% 4.36/1.78  #Tautology    : 67
% 4.36/1.78  #SimpNegUnit  : 8
% 4.36/1.78  #BackRed      : 0
% 4.36/1.78  
% 4.36/1.78  #Partial instantiations: 0
% 4.36/1.78  #Strategies tried      : 1
% 4.36/1.78  
% 4.36/1.78  Timing (in seconds)
% 4.36/1.78  ----------------------
% 4.82/1.78  Preprocessing        : 0.43
% 4.82/1.78  Parsing              : 0.21
% 4.82/1.78  CNF conversion       : 0.07
% 4.82/1.78  Main loop            : 0.57
% 4.82/1.78  Inferencing          : 0.20
% 4.82/1.78  Reduction            : 0.17
% 4.82/1.78  Demodulation         : 0.12
% 4.82/1.78  BG Simplification    : 0.03
% 4.82/1.78  Subsumption          : 0.13
% 4.82/1.78  Abstraction          : 0.03
% 4.82/1.78  MUC search           : 0.00
% 4.82/1.78  Cooper               : 0.00
% 4.82/1.78  Total                : 1.04
% 4.82/1.78  Index Insertion      : 0.00
% 4.82/1.78  Index Deletion       : 0.00
% 4.82/1.78  Index Matching       : 0.00
% 4.82/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
