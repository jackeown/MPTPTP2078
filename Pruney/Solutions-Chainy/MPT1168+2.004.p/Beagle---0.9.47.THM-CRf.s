%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:52 EST 2020

% Result     : Theorem 24.62s
% Output     : CNFRefutation 24.67s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 309 expanded)
%              Number of leaves         :   32 ( 130 expanded)
%              Depth                    :   20
%              Number of atoms          :  535 (1536 expanded)
%              Number of equality atoms :   20 (  93 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > m1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_191,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( ( r2_hidden(B,C)
                        & m1_orders_2(C,A,D) )
                     => k3_orders_2(A,C,B) = k3_orders_2(A,D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_orders_2)).

tff(f_131,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_orders_2(C,A,B)
             => r1_tarski(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r1_tarski(C,D)
                   => r1_tarski(k3_orders_2(A,C,B),k3_orders_2(A,D,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_164,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ! [E] :
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(A)))
                     => ( ( r2_orders_2(A,B,C)
                          & r2_hidden(B,D)
                          & r2_hidden(C,E)
                          & m1_orders_2(E,A,D) )
                       => r2_hidden(B,E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_orders_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(c_32,plain,(
    k3_orders_2('#skF_4','#skF_7','#skF_5') != k3_orders_2('#skF_4','#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_50,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_48,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_46,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_44,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_34,plain,(
    m1_orders_2('#skF_6','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_120,plain,(
    ! [C_121,B_122,A_123] :
      ( r1_tarski(C_121,B_122)
      | ~ m1_orders_2(C_121,A_123,B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ l1_orders_2(A_123)
      | ~ v5_orders_2(A_123)
      | ~ v4_orders_2(A_123)
      | ~ v3_orders_2(A_123)
      | v2_struct_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_122,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_120])).

tff(c_125,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_38,c_122])).

tff(c_126,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_125])).

tff(c_26,plain,(
    ! [A_30,C_42,B_38,D_44] :
      ( r1_tarski(k3_orders_2(A_30,C_42,B_38),k3_orders_2(A_30,D_44,B_38))
      | ~ r1_tarski(C_42,D_44)
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_subset_1(C_42,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_subset_1(B_38,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30)
      | ~ v5_orders_2(A_30)
      | ~ v4_orders_2(A_30)
      | ~ v3_orders_2(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    ! [A_96,B_97] :
      ( ~ r2_hidden('#skF_1'(A_96,B_97),B_97)
      | r1_tarski(A_96,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_54])).

tff(c_193,plain,(
    ! [A_139,B_140,C_141] :
      ( m1_subset_1(k3_orders_2(A_139,B_140,C_141),k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ m1_subset_1(C_141,u1_struct_0(A_139))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_orders_2(A_139)
      | ~ v5_orders_2(A_139)
      | ~ v4_orders_2(A_139)
      | ~ v3_orders_2(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    ! [A_9,C_11,B_10] :
      ( m1_subset_1(A_9,C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1358,plain,(
    ! [A_285,A_286,B_287,C_288] :
      ( m1_subset_1(A_285,u1_struct_0(A_286))
      | ~ r2_hidden(A_285,k3_orders_2(A_286,B_287,C_288))
      | ~ m1_subset_1(C_288,u1_struct_0(A_286))
      | ~ m1_subset_1(B_287,k1_zfmisc_1(u1_struct_0(A_286)))
      | ~ l1_orders_2(A_286)
      | ~ v5_orders_2(A_286)
      | ~ v4_orders_2(A_286)
      | ~ v3_orders_2(A_286)
      | v2_struct_0(A_286) ) ),
    inference(resolution,[status(thm)],[c_193,c_16])).

tff(c_2874,plain,(
    ! [A_524,B_525,C_526,B_527] :
      ( m1_subset_1('#skF_1'(k3_orders_2(A_524,B_525,C_526),B_527),u1_struct_0(A_524))
      | ~ m1_subset_1(C_526,u1_struct_0(A_524))
      | ~ m1_subset_1(B_525,k1_zfmisc_1(u1_struct_0(A_524)))
      | ~ l1_orders_2(A_524)
      | ~ v5_orders_2(A_524)
      | ~ v4_orders_2(A_524)
      | ~ v3_orders_2(A_524)
      | v2_struct_0(A_524)
      | r1_tarski(k3_orders_2(A_524,B_525,C_526),B_527) ) ),
    inference(resolution,[status(thm)],[c_6,c_1358])).

tff(c_286,plain,(
    ! [B_163,D_164,A_165,C_166] :
      ( r2_hidden(B_163,D_164)
      | ~ r2_hidden(B_163,k3_orders_2(A_165,D_164,C_166))
      | ~ m1_subset_1(D_164,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ m1_subset_1(C_166,u1_struct_0(A_165))
      | ~ m1_subset_1(B_163,u1_struct_0(A_165))
      | ~ l1_orders_2(A_165)
      | ~ v5_orders_2(A_165)
      | ~ v4_orders_2(A_165)
      | ~ v3_orders_2(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_342,plain,(
    ! [A_165,D_164,C_166,B_2] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_165,D_164,C_166),B_2),D_164)
      | ~ m1_subset_1(D_164,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ m1_subset_1(C_166,u1_struct_0(A_165))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_165,D_164,C_166),B_2),u1_struct_0(A_165))
      | ~ l1_orders_2(A_165)
      | ~ v5_orders_2(A_165)
      | ~ v4_orders_2(A_165)
      | ~ v3_orders_2(A_165)
      | v2_struct_0(A_165)
      | r1_tarski(k3_orders_2(A_165,D_164,C_166),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_286])).

tff(c_2881,plain,(
    ! [A_528,B_529,C_530,B_531] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_528,B_529,C_530),B_531),B_529)
      | ~ m1_subset_1(C_530,u1_struct_0(A_528))
      | ~ m1_subset_1(B_529,k1_zfmisc_1(u1_struct_0(A_528)))
      | ~ l1_orders_2(A_528)
      | ~ v5_orders_2(A_528)
      | ~ v4_orders_2(A_528)
      | ~ v3_orders_2(A_528)
      | v2_struct_0(A_528)
      | r1_tarski(k3_orders_2(A_528,B_529,C_530),B_531) ) ),
    inference(resolution,[status(thm)],[c_2874,c_342])).

tff(c_68,plain,(
    ! [A_102,C_103,B_104] :
      ( m1_subset_1(A_102,C_103)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(C_103))
      | ~ r2_hidden(A_102,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_74,plain,(
    ! [A_102] :
      ( m1_subset_1(A_102,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_102,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_38,c_68])).

tff(c_1731,plain,(
    ! [A_316,D_317,C_318,B_319] :
      ( r2_hidden('#skF_1'(k3_orders_2(A_316,D_317,C_318),B_319),D_317)
      | ~ m1_subset_1(D_317,k1_zfmisc_1(u1_struct_0(A_316)))
      | ~ m1_subset_1(C_318,u1_struct_0(A_316))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_316,D_317,C_318),B_319),u1_struct_0(A_316))
      | ~ l1_orders_2(A_316)
      | ~ v5_orders_2(A_316)
      | ~ v4_orders_2(A_316)
      | ~ v3_orders_2(A_316)
      | v2_struct_0(A_316)
      | r1_tarski(k3_orders_2(A_316,D_317,C_318),B_319) ) ),
    inference(resolution,[status(thm)],[c_6,c_286])).

tff(c_1734,plain,(
    ! [D_317,C_318,B_319] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_4',D_317,C_318),B_319),D_317)
      | ~ m1_subset_1(D_317,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(C_318,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | r1_tarski(k3_orders_2('#skF_4',D_317,C_318),B_319)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_4',D_317,C_318),B_319),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_74,c_1731])).

tff(c_1740,plain,(
    ! [D_317,C_318,B_319] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_4',D_317,C_318),B_319),D_317)
      | ~ m1_subset_1(D_317,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(C_318,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | r1_tarski(k3_orders_2('#skF_4',D_317,C_318),B_319)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_4',D_317,C_318),B_319),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_1734])).

tff(c_1741,plain,(
    ! [D_317,C_318,B_319] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_4',D_317,C_318),B_319),D_317)
      | ~ m1_subset_1(D_317,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(C_318,u1_struct_0('#skF_4'))
      | r1_tarski(k3_orders_2('#skF_4',D_317,C_318),B_319)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_4',D_317,C_318),B_319),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1740])).

tff(c_2884,plain,(
    ! [C_530,B_531] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_4','#skF_7',C_530),B_531),'#skF_7')
      | ~ m1_subset_1(C_530,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | r1_tarski(k3_orders_2('#skF_4','#skF_7',C_530),B_531) ) ),
    inference(resolution,[status(thm)],[c_2881,c_1741])).

tff(c_2905,plain,(
    ! [C_530,B_531] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_4','#skF_7',C_530),B_531),'#skF_7')
      | ~ m1_subset_1(C_530,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | r1_tarski(k3_orders_2('#skF_4','#skF_7',C_530),B_531) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_38,c_2884])).

tff(c_2916,plain,(
    ! [C_532,B_533] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_4','#skF_7',C_532),B_533),'#skF_7')
      | ~ m1_subset_1(C_532,u1_struct_0('#skF_4'))
      | r1_tarski(k3_orders_2('#skF_4','#skF_7',C_532),B_533) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2905])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2928,plain,(
    ! [C_532,B_533,B_2] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_4','#skF_7',C_532),B_533),B_2)
      | ~ r1_tarski('#skF_7',B_2)
      | ~ m1_subset_1(C_532,u1_struct_0('#skF_4'))
      | r1_tarski(k3_orders_2('#skF_4','#skF_7',C_532),B_533) ) ),
    inference(resolution,[status(thm)],[c_2916,c_2])).

tff(c_61,plain,(
    ! [C_99,B_100,A_101] :
      ( r2_hidden(C_99,B_100)
      | ~ r2_hidden(C_99,A_101)
      | ~ r1_tarski(A_101,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_66,plain,(
    ! [A_1,B_2,B_100] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_100)
      | ~ r1_tarski(A_1,B_100)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_61])).

tff(c_483,plain,(
    ! [A_185,B_186,C_187,D_188] :
      ( r2_orders_2(A_185,B_186,C_187)
      | ~ r2_hidden(B_186,k3_orders_2(A_185,D_188,C_187))
      | ~ m1_subset_1(D_188,k1_zfmisc_1(u1_struct_0(A_185)))
      | ~ m1_subset_1(C_187,u1_struct_0(A_185))
      | ~ m1_subset_1(B_186,u1_struct_0(A_185))
      | ~ l1_orders_2(A_185)
      | ~ v5_orders_2(A_185)
      | ~ v4_orders_2(A_185)
      | ~ v3_orders_2(A_185)
      | v2_struct_0(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_7409,plain,(
    ! [D_931,B_929,A_927,C_928,A_930] :
      ( r2_orders_2(A_927,'#skF_1'(A_930,B_929),C_928)
      | ~ m1_subset_1(D_931,k1_zfmisc_1(u1_struct_0(A_927)))
      | ~ m1_subset_1(C_928,u1_struct_0(A_927))
      | ~ m1_subset_1('#skF_1'(A_930,B_929),u1_struct_0(A_927))
      | ~ l1_orders_2(A_927)
      | ~ v5_orders_2(A_927)
      | ~ v4_orders_2(A_927)
      | ~ v3_orders_2(A_927)
      | v2_struct_0(A_927)
      | ~ r1_tarski(A_930,k3_orders_2(A_927,D_931,C_928))
      | r1_tarski(A_930,B_929) ) ),
    inference(resolution,[status(thm)],[c_66,c_483])).

tff(c_7415,plain,(
    ! [A_930,B_929,C_928] :
      ( r2_orders_2('#skF_4','#skF_1'(A_930,B_929),C_928)
      | ~ m1_subset_1(C_928,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_930,B_929),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_930,k3_orders_2('#skF_4','#skF_7',C_928))
      | r1_tarski(A_930,B_929) ) ),
    inference(resolution,[status(thm)],[c_38,c_7409])).

tff(c_7423,plain,(
    ! [A_930,B_929,C_928] :
      ( r2_orders_2('#skF_4','#skF_1'(A_930,B_929),C_928)
      | ~ m1_subset_1(C_928,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_930,B_929),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_930,k3_orders_2('#skF_4','#skF_7',C_928))
      | r1_tarski(A_930,B_929) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_7415])).

tff(c_7489,plain,(
    ! [A_941,B_942,C_943] :
      ( r2_orders_2('#skF_4','#skF_1'(A_941,B_942),C_943)
      | ~ m1_subset_1(C_943,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_941,B_942),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_941,k3_orders_2('#skF_4','#skF_7',C_943))
      | r1_tarski(A_941,B_942) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_7423])).

tff(c_7517,plain,(
    ! [A_944,B_945,C_946] :
      ( r2_orders_2('#skF_4','#skF_1'(A_944,B_945),C_946)
      | ~ m1_subset_1(C_946,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_944,k3_orders_2('#skF_4','#skF_7',C_946))
      | r1_tarski(A_944,B_945)
      | ~ r2_hidden('#skF_1'(A_944,B_945),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_74,c_7489])).

tff(c_1255,plain,(
    ! [B_261,C_263,D_260,E_264,A_262] :
      ( r2_hidden(B_261,E_264)
      | ~ m1_orders_2(E_264,A_262,D_260)
      | ~ r2_hidden(C_263,E_264)
      | ~ r2_hidden(B_261,D_260)
      | ~ r2_orders_2(A_262,B_261,C_263)
      | ~ m1_subset_1(E_264,k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ m1_subset_1(D_260,k1_zfmisc_1(u1_struct_0(A_262)))
      | ~ m1_subset_1(C_263,u1_struct_0(A_262))
      | ~ m1_subset_1(B_261,u1_struct_0(A_262))
      | ~ l1_orders_2(A_262)
      | ~ v5_orders_2(A_262)
      | ~ v4_orders_2(A_262)
      | ~ v3_orders_2(A_262)
      | v2_struct_0(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1257,plain,(
    ! [B_261,C_263] :
      ( r2_hidden(B_261,'#skF_6')
      | ~ r2_hidden(C_263,'#skF_6')
      | ~ r2_hidden(B_261,'#skF_7')
      | ~ r2_orders_2('#skF_4',B_261,C_263)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(C_263,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_261,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_1255])).

tff(c_1260,plain,(
    ! [B_261,C_263] :
      ( r2_hidden(B_261,'#skF_6')
      | ~ r2_hidden(C_263,'#skF_6')
      | ~ r2_hidden(B_261,'#skF_7')
      | ~ r2_orders_2('#skF_4',B_261,C_263)
      | ~ m1_subset_1(C_263,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_261,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_38,c_40,c_1257])).

tff(c_1261,plain,(
    ! [B_261,C_263] :
      ( r2_hidden(B_261,'#skF_6')
      | ~ r2_hidden(C_263,'#skF_6')
      | ~ r2_hidden(B_261,'#skF_7')
      | ~ r2_orders_2('#skF_4',B_261,C_263)
      | ~ m1_subset_1(C_263,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_261,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1260])).

tff(c_23253,plain,(
    ! [A_1746,B_1747,C_1748] :
      ( r2_hidden('#skF_1'(A_1746,B_1747),'#skF_6')
      | ~ r2_hidden(C_1748,'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_1746,B_1747),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_1748,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_1746,k3_orders_2('#skF_4','#skF_7',C_1748))
      | r1_tarski(A_1746,B_1747)
      | ~ r2_hidden('#skF_1'(A_1746,B_1747),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_7517,c_1261])).

tff(c_23281,plain,(
    ! [A_1749,B_1750,C_1751] :
      ( r2_hidden('#skF_1'(A_1749,B_1750),'#skF_6')
      | ~ r2_hidden(C_1751,'#skF_6')
      | ~ m1_subset_1(C_1751,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_1749,k3_orders_2('#skF_4','#skF_7',C_1751))
      | r1_tarski(A_1749,B_1750)
      | ~ r2_hidden('#skF_1'(A_1749,B_1750),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_74,c_23253])).

tff(c_23335,plain,(
    ! [C_1752,B_1753] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_4','#skF_7',C_1752),B_1753),'#skF_6')
      | ~ r2_hidden(C_1752,'#skF_6')
      | ~ m1_subset_1(C_1752,u1_struct_0('#skF_4'))
      | r1_tarski(k3_orders_2('#skF_4','#skF_7',C_1752),B_1753)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_4','#skF_7',C_1752),B_1753),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_59,c_23281])).

tff(c_23371,plain,(
    ! [C_532,B_533] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_4','#skF_7',C_532),B_533),'#skF_6')
      | ~ r2_hidden(C_532,'#skF_6')
      | ~ r1_tarski('#skF_7','#skF_7')
      | ~ m1_subset_1(C_532,u1_struct_0('#skF_4'))
      | r1_tarski(k3_orders_2('#skF_4','#skF_7',C_532),B_533) ) ),
    inference(resolution,[status(thm)],[c_2928,c_23335])).

tff(c_23437,plain,(
    ! [C_532,B_533] :
      ( r2_hidden('#skF_1'(k3_orders_2('#skF_4','#skF_7',C_532),B_533),'#skF_6')
      | ~ r2_hidden(C_532,'#skF_6')
      | ~ m1_subset_1(C_532,u1_struct_0('#skF_4'))
      | r1_tarski(k3_orders_2('#skF_4','#skF_7',C_532),B_533) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_23371])).

tff(c_3683,plain,(
    ! [A_562,A_563,C_561,B_559,B_560] :
      ( m1_subset_1('#skF_1'(A_562,B_560),u1_struct_0(A_563))
      | ~ m1_subset_1(C_561,u1_struct_0(A_563))
      | ~ m1_subset_1(B_559,k1_zfmisc_1(u1_struct_0(A_563)))
      | ~ l1_orders_2(A_563)
      | ~ v5_orders_2(A_563)
      | ~ v4_orders_2(A_563)
      | ~ v3_orders_2(A_563)
      | v2_struct_0(A_563)
      | ~ r1_tarski(A_562,k3_orders_2(A_563,B_559,C_561))
      | r1_tarski(A_562,B_560) ) ),
    inference(resolution,[status(thm)],[c_66,c_1358])).

tff(c_3689,plain,(
    ! [A_562,B_560,C_561] :
      ( m1_subset_1('#skF_1'(A_562,B_560),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_561,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_562,k3_orders_2('#skF_4','#skF_7',C_561))
      | r1_tarski(A_562,B_560) ) ),
    inference(resolution,[status(thm)],[c_38,c_3683])).

tff(c_3697,plain,(
    ! [A_562,B_560,C_561] :
      ( m1_subset_1('#skF_1'(A_562,B_560),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_561,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(A_562,k3_orders_2('#skF_4','#skF_7',C_561))
      | r1_tarski(A_562,B_560) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_3689])).

tff(c_3924,plain,(
    ! [A_576,B_577,C_578] :
      ( m1_subset_1('#skF_1'(A_576,B_577),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_578,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_576,k3_orders_2('#skF_4','#skF_7',C_578))
      | r1_tarski(A_576,B_577) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3697])).

tff(c_3949,plain,(
    ! [C_578,B_577] :
      ( m1_subset_1('#skF_1'(k3_orders_2('#skF_4','#skF_7',C_578),B_577),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_578,u1_struct_0('#skF_4'))
      | r1_tarski(k3_orders_2('#skF_4','#skF_7',C_578),B_577) ) ),
    inference(resolution,[status(thm)],[c_59,c_3924])).

tff(c_73,plain,(
    ! [A_102] :
      ( m1_subset_1(A_102,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_102,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_40,c_68])).

tff(c_1885,plain,(
    ! [A_350,D_351,C_352,B_353] :
      ( r2_orders_2(A_350,'#skF_1'(k3_orders_2(A_350,D_351,C_352),B_353),C_352)
      | ~ m1_subset_1(D_351,k1_zfmisc_1(u1_struct_0(A_350)))
      | ~ m1_subset_1(C_352,u1_struct_0(A_350))
      | ~ m1_subset_1('#skF_1'(k3_orders_2(A_350,D_351,C_352),B_353),u1_struct_0(A_350))
      | ~ l1_orders_2(A_350)
      | ~ v5_orders_2(A_350)
      | ~ v4_orders_2(A_350)
      | ~ v3_orders_2(A_350)
      | v2_struct_0(A_350)
      | r1_tarski(k3_orders_2(A_350,D_351,C_352),B_353) ) ),
    inference(resolution,[status(thm)],[c_6,c_483])).

tff(c_1891,plain,(
    ! [D_351,C_352,B_353] :
      ( r2_orders_2('#skF_4','#skF_1'(k3_orders_2('#skF_4',D_351,C_352),B_353),C_352)
      | ~ m1_subset_1(D_351,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(C_352,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | r1_tarski(k3_orders_2('#skF_4',D_351,C_352),B_353)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_4',D_351,C_352),B_353),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_73,c_1885])).

tff(c_1898,plain,(
    ! [D_351,C_352,B_353] :
      ( r2_orders_2('#skF_4','#skF_1'(k3_orders_2('#skF_4',D_351,C_352),B_353),C_352)
      | ~ m1_subset_1(D_351,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(C_352,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | r1_tarski(k3_orders_2('#skF_4',D_351,C_352),B_353)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_4',D_351,C_352),B_353),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_1891])).

tff(c_1899,plain,(
    ! [D_351,C_352,B_353] :
      ( r2_orders_2('#skF_4','#skF_1'(k3_orders_2('#skF_4',D_351,C_352),B_353),C_352)
      | ~ m1_subset_1(D_351,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(C_352,u1_struct_0('#skF_4'))
      | r1_tarski(k3_orders_2('#skF_4',D_351,C_352),B_353)
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_4',D_351,C_352),B_353),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1898])).

tff(c_654,plain,(
    ! [B_208,A_209,D_210,C_211] :
      ( r2_hidden(B_208,k3_orders_2(A_209,D_210,C_211))
      | ~ r2_hidden(B_208,D_210)
      | ~ r2_orders_2(A_209,B_208,C_211)
      | ~ m1_subset_1(D_210,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ m1_subset_1(C_211,u1_struct_0(A_209))
      | ~ m1_subset_1(B_208,u1_struct_0(A_209))
      | ~ l1_orders_2(A_209)
      | ~ v5_orders_2(A_209)
      | ~ v4_orders_2(A_209)
      | ~ v3_orders_2(A_209)
      | v2_struct_0(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_658,plain,(
    ! [B_208,C_211] :
      ( r2_hidden(B_208,k3_orders_2('#skF_4','#skF_6',C_211))
      | ~ r2_hidden(B_208,'#skF_6')
      | ~ r2_orders_2('#skF_4',B_208,C_211)
      | ~ m1_subset_1(C_211,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_208,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_654])).

tff(c_664,plain,(
    ! [B_208,C_211] :
      ( r2_hidden(B_208,k3_orders_2('#skF_4','#skF_6',C_211))
      | ~ r2_hidden(B_208,'#skF_6')
      | ~ r2_orders_2('#skF_4',B_208,C_211)
      | ~ m1_subset_1(C_211,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_208,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_658])).

tff(c_1023,plain,(
    ! [B_246,C_247] :
      ( r2_hidden(B_246,k3_orders_2('#skF_4','#skF_6',C_247))
      | ~ r2_hidden(B_246,'#skF_6')
      | ~ r2_orders_2('#skF_4',B_246,C_247)
      | ~ m1_subset_1(C_247,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_246,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_664])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3964,plain,(
    ! [A_583,C_584] :
      ( r1_tarski(A_583,k3_orders_2('#skF_4','#skF_6',C_584))
      | ~ r2_hidden('#skF_1'(A_583,k3_orders_2('#skF_4','#skF_6',C_584)),'#skF_6')
      | ~ r2_orders_2('#skF_4','#skF_1'(A_583,k3_orders_2('#skF_4','#skF_6',C_584)),C_584)
      | ~ m1_subset_1(C_584,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_1'(A_583,k3_orders_2('#skF_4','#skF_6',C_584)),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1023,c_4])).

tff(c_34044,plain,(
    ! [D_2177,C_2178] :
      ( ~ m1_subset_1('#skF_1'(k3_orders_2('#skF_4',D_2177,C_2178),k3_orders_2('#skF_4','#skF_6',C_2178)),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(D_2177,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(C_2178,u1_struct_0('#skF_4'))
      | r1_tarski(k3_orders_2('#skF_4',D_2177,C_2178),k3_orders_2('#skF_4','#skF_6',C_2178))
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_4',D_2177,C_2178),k3_orders_2('#skF_4','#skF_6',C_2178)),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1899,c_3964])).

tff(c_34056,plain,(
    ! [C_578] :
      ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r2_hidden('#skF_1'(k3_orders_2('#skF_4','#skF_7',C_578),k3_orders_2('#skF_4','#skF_6',C_578)),'#skF_6')
      | ~ m1_subset_1(C_578,u1_struct_0('#skF_4'))
      | r1_tarski(k3_orders_2('#skF_4','#skF_7',C_578),k3_orders_2('#skF_4','#skF_6',C_578)) ) ),
    inference(resolution,[status(thm)],[c_3949,c_34044])).

tff(c_34085,plain,(
    ! [C_2179] :
      ( ~ r2_hidden('#skF_1'(k3_orders_2('#skF_4','#skF_7',C_2179),k3_orders_2('#skF_4','#skF_6',C_2179)),'#skF_6')
      | ~ m1_subset_1(C_2179,u1_struct_0('#skF_4'))
      | r1_tarski(k3_orders_2('#skF_4','#skF_7',C_2179),k3_orders_2('#skF_4','#skF_6',C_2179)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34056])).

tff(c_34181,plain,(
    ! [C_2180] :
      ( ~ r2_hidden(C_2180,'#skF_6')
      | ~ m1_subset_1(C_2180,u1_struct_0('#skF_4'))
      | r1_tarski(k3_orders_2('#skF_4','#skF_7',C_2180),k3_orders_2('#skF_4','#skF_6',C_2180)) ) ),
    inference(resolution,[status(thm)],[c_23437,c_34085])).

tff(c_106,plain,(
    ! [A_119,B_120] :
      ( r2_hidden('#skF_2'(A_119,B_120),B_120)
      | r2_hidden('#skF_3'(A_119,B_120),A_119)
      | B_120 = A_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_235,plain,(
    ! [A_155,B_156,B_157] :
      ( r2_hidden('#skF_3'(A_155,B_156),B_157)
      | ~ r1_tarski(A_155,B_157)
      | r2_hidden('#skF_2'(A_155,B_156),B_156)
      | B_156 = A_155 ) ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_256,plain,(
    ! [A_158,B_159] :
      ( ~ r1_tarski(A_158,B_159)
      | r2_hidden('#skF_2'(A_158,B_159),B_159)
      | B_159 = A_158 ) ),
    inference(resolution,[status(thm)],[c_235,c_10])).

tff(c_274,plain,(
    ! [A_160,B_161,B_162] :
      ( r2_hidden('#skF_2'(A_160,B_161),B_162)
      | ~ r1_tarski(B_161,B_162)
      | ~ r1_tarski(A_160,B_161)
      | B_161 = A_160 ) ),
    inference(resolution,[status(thm)],[c_256,c_2])).

tff(c_94,plain,(
    ! [A_113,B_114] :
      ( ~ r2_hidden('#skF_2'(A_113,B_114),A_113)
      | r2_hidden('#skF_3'(A_113,B_114),A_113)
      | B_114 = A_113 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_97,plain,(
    ! [A_113,B_114,B_2] :
      ( r2_hidden('#skF_3'(A_113,B_114),B_2)
      | ~ r1_tarski(A_113,B_2)
      | ~ r2_hidden('#skF_2'(A_113,B_114),A_113)
      | B_114 = A_113 ) ),
    inference(resolution,[status(thm)],[c_94,c_2])).

tff(c_438,plain,(
    ! [B_179,B_180,B_181] :
      ( r2_hidden('#skF_3'(B_179,B_180),B_181)
      | ~ r1_tarski(B_179,B_181)
      | ~ r1_tarski(B_180,B_179)
      | ~ r1_tarski(B_179,B_180)
      | B_180 = B_179 ) ),
    inference(resolution,[status(thm)],[c_274,c_97])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7),A_6)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_284,plain,(
    ! [B_162,B_161] :
      ( ~ r2_hidden('#skF_3'(B_162,B_161),B_161)
      | ~ r1_tarski(B_161,B_162)
      | ~ r1_tarski(B_162,B_161)
      | B_162 = B_161 ) ),
    inference(resolution,[status(thm)],[c_274,c_8])).

tff(c_457,plain,(
    ! [B_181,B_179] :
      ( ~ r1_tarski(B_181,B_179)
      | ~ r1_tarski(B_179,B_181)
      | B_181 = B_179 ) ),
    inference(resolution,[status(thm)],[c_438,c_284])).

tff(c_36899,plain,(
    ! [C_2222] :
      ( ~ r1_tarski(k3_orders_2('#skF_4','#skF_6',C_2222),k3_orders_2('#skF_4','#skF_7',C_2222))
      | k3_orders_2('#skF_4','#skF_7',C_2222) = k3_orders_2('#skF_4','#skF_6',C_2222)
      | ~ r2_hidden(C_2222,'#skF_6')
      | ~ m1_subset_1(C_2222,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_34181,c_457])).

tff(c_36911,plain,(
    ! [B_38] :
      ( k3_orders_2('#skF_4','#skF_7',B_38) = k3_orders_2('#skF_4','#skF_6',B_38)
      | ~ r2_hidden(B_38,'#skF_6')
      | ~ r1_tarski('#skF_6','#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_36899])).

tff(c_36916,plain,(
    ! [B_38] :
      ( k3_orders_2('#skF_4','#skF_7',B_38) = k3_orders_2('#skF_4','#skF_6',B_38)
      | ~ r2_hidden(B_38,'#skF_6')
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_40,c_38,c_126,c_36911])).

tff(c_37026,plain,(
    ! [B_2227] :
      ( k3_orders_2('#skF_4','#skF_7',B_2227) = k3_orders_2('#skF_4','#skF_6',B_2227)
      | ~ r2_hidden(B_2227,'#skF_6')
      | ~ m1_subset_1(B_2227,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_36916])).

tff(c_37135,plain,
    ( k3_orders_2('#skF_4','#skF_7','#skF_5') = k3_orders_2('#skF_4','#skF_6','#skF_5')
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_37026])).

tff(c_37192,plain,(
    k3_orders_2('#skF_4','#skF_7','#skF_5') = k3_orders_2('#skF_4','#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_37135])).

tff(c_37194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_37192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.62/16.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.67/16.91  
% 24.67/16.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.67/16.91  %$ r2_orders_2 > m1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 24.67/16.91  
% 24.67/16.91  %Foreground sorts:
% 24.67/16.91  
% 24.67/16.91  
% 24.67/16.91  %Background operators:
% 24.67/16.91  
% 24.67/16.91  
% 24.67/16.91  %Foreground operators:
% 24.67/16.91  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 24.67/16.91  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 24.67/16.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.67/16.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.67/16.91  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 24.67/16.91  tff('#skF_7', type, '#skF_7': $i).
% 24.67/16.91  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 24.67/16.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.67/16.91  tff('#skF_5', type, '#skF_5': $i).
% 24.67/16.91  tff('#skF_6', type, '#skF_6': $i).
% 24.67/16.91  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 24.67/16.91  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 24.67/16.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 24.67/16.91  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 24.67/16.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.67/16.91  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 24.67/16.91  tff('#skF_4', type, '#skF_4': $i).
% 24.67/16.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.67/16.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 24.67/16.91  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 24.67/16.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 24.67/16.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 24.67/16.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 24.67/16.91  
% 24.67/16.93  tff(f_191, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, C) & m1_orders_2(C, A, D)) => (k3_orders_2(A, C, B) = k3_orders_2(A, D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_orders_2)).
% 24.67/16.93  tff(f_131, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_orders_2(C, A, B) => r1_tarski(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 24.67/16.93  tff(f_112, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, D) => r1_tarski(k3_orders_2(A, C, B), k3_orders_2(A, D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_orders_2)).
% 24.67/16.93  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 24.67/16.93  tff(f_62, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 24.67/16.93  tff(f_45, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 24.67/16.93  tff(f_88, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 24.67/16.93  tff(f_164, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(A))) => ((((r2_orders_2(A, B, C) & r2_hidden(B, D)) & r2_hidden(C, E)) & m1_orders_2(E, A, D)) => r2_hidden(B, E)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_orders_2)).
% 24.67/16.93  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 24.67/16.93  tff(c_32, plain, (k3_orders_2('#skF_4', '#skF_7', '#skF_5')!=k3_orders_2('#skF_4', '#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_191])).
% 24.67/16.93  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_191])).
% 24.67/16.93  tff(c_42, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 24.67/16.93  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_191])).
% 24.67/16.93  tff(c_50, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_191])).
% 24.67/16.93  tff(c_48, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_191])).
% 24.67/16.93  tff(c_46, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_191])).
% 24.67/16.93  tff(c_44, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_191])).
% 24.67/16.93  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_191])).
% 24.67/16.93  tff(c_38, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_191])).
% 24.67/16.93  tff(c_34, plain, (m1_orders_2('#skF_6', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_191])).
% 24.67/16.93  tff(c_120, plain, (![C_121, B_122, A_123]: (r1_tarski(C_121, B_122) | ~m1_orders_2(C_121, A_123, B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(u1_struct_0(A_123))) | ~l1_orders_2(A_123) | ~v5_orders_2(A_123) | ~v4_orders_2(A_123) | ~v3_orders_2(A_123) | v2_struct_0(A_123))), inference(cnfTransformation, [status(thm)], [f_131])).
% 24.67/16.93  tff(c_122, plain, (r1_tarski('#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_120])).
% 24.67/16.93  tff(c_125, plain, (r1_tarski('#skF_6', '#skF_7') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_38, c_122])).
% 24.67/16.93  tff(c_126, plain, (r1_tarski('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_52, c_125])).
% 24.67/16.93  tff(c_26, plain, (![A_30, C_42, B_38, D_44]: (r1_tarski(k3_orders_2(A_30, C_42, B_38), k3_orders_2(A_30, D_44, B_38)) | ~r1_tarski(C_42, D_44) | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(C_42, k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(B_38, u1_struct_0(A_30)) | ~l1_orders_2(A_30) | ~v5_orders_2(A_30) | ~v4_orders_2(A_30) | ~v3_orders_2(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_112])).
% 24.67/16.93  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 24.67/16.93  tff(c_54, plain, (![A_96, B_97]: (~r2_hidden('#skF_1'(A_96, B_97), B_97) | r1_tarski(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_32])).
% 24.67/16.93  tff(c_59, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_54])).
% 24.67/16.93  tff(c_193, plain, (![A_139, B_140, C_141]: (m1_subset_1(k3_orders_2(A_139, B_140, C_141), k1_zfmisc_1(u1_struct_0(A_139))) | ~m1_subset_1(C_141, u1_struct_0(A_139)) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_orders_2(A_139) | ~v5_orders_2(A_139) | ~v4_orders_2(A_139) | ~v3_orders_2(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_62])).
% 24.67/16.93  tff(c_16, plain, (![A_9, C_11, B_10]: (m1_subset_1(A_9, C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 24.67/16.93  tff(c_1358, plain, (![A_285, A_286, B_287, C_288]: (m1_subset_1(A_285, u1_struct_0(A_286)) | ~r2_hidden(A_285, k3_orders_2(A_286, B_287, C_288)) | ~m1_subset_1(C_288, u1_struct_0(A_286)) | ~m1_subset_1(B_287, k1_zfmisc_1(u1_struct_0(A_286))) | ~l1_orders_2(A_286) | ~v5_orders_2(A_286) | ~v4_orders_2(A_286) | ~v3_orders_2(A_286) | v2_struct_0(A_286))), inference(resolution, [status(thm)], [c_193, c_16])).
% 24.67/16.93  tff(c_2874, plain, (![A_524, B_525, C_526, B_527]: (m1_subset_1('#skF_1'(k3_orders_2(A_524, B_525, C_526), B_527), u1_struct_0(A_524)) | ~m1_subset_1(C_526, u1_struct_0(A_524)) | ~m1_subset_1(B_525, k1_zfmisc_1(u1_struct_0(A_524))) | ~l1_orders_2(A_524) | ~v5_orders_2(A_524) | ~v4_orders_2(A_524) | ~v3_orders_2(A_524) | v2_struct_0(A_524) | r1_tarski(k3_orders_2(A_524, B_525, C_526), B_527))), inference(resolution, [status(thm)], [c_6, c_1358])).
% 24.67/16.93  tff(c_286, plain, (![B_163, D_164, A_165, C_166]: (r2_hidden(B_163, D_164) | ~r2_hidden(B_163, k3_orders_2(A_165, D_164, C_166)) | ~m1_subset_1(D_164, k1_zfmisc_1(u1_struct_0(A_165))) | ~m1_subset_1(C_166, u1_struct_0(A_165)) | ~m1_subset_1(B_163, u1_struct_0(A_165)) | ~l1_orders_2(A_165) | ~v5_orders_2(A_165) | ~v4_orders_2(A_165) | ~v3_orders_2(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_88])).
% 24.67/16.93  tff(c_342, plain, (![A_165, D_164, C_166, B_2]: (r2_hidden('#skF_1'(k3_orders_2(A_165, D_164, C_166), B_2), D_164) | ~m1_subset_1(D_164, k1_zfmisc_1(u1_struct_0(A_165))) | ~m1_subset_1(C_166, u1_struct_0(A_165)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_165, D_164, C_166), B_2), u1_struct_0(A_165)) | ~l1_orders_2(A_165) | ~v5_orders_2(A_165) | ~v4_orders_2(A_165) | ~v3_orders_2(A_165) | v2_struct_0(A_165) | r1_tarski(k3_orders_2(A_165, D_164, C_166), B_2))), inference(resolution, [status(thm)], [c_6, c_286])).
% 24.67/16.93  tff(c_2881, plain, (![A_528, B_529, C_530, B_531]: (r2_hidden('#skF_1'(k3_orders_2(A_528, B_529, C_530), B_531), B_529) | ~m1_subset_1(C_530, u1_struct_0(A_528)) | ~m1_subset_1(B_529, k1_zfmisc_1(u1_struct_0(A_528))) | ~l1_orders_2(A_528) | ~v5_orders_2(A_528) | ~v4_orders_2(A_528) | ~v3_orders_2(A_528) | v2_struct_0(A_528) | r1_tarski(k3_orders_2(A_528, B_529, C_530), B_531))), inference(resolution, [status(thm)], [c_2874, c_342])).
% 24.67/16.93  tff(c_68, plain, (![A_102, C_103, B_104]: (m1_subset_1(A_102, C_103) | ~m1_subset_1(B_104, k1_zfmisc_1(C_103)) | ~r2_hidden(A_102, B_104))), inference(cnfTransformation, [status(thm)], [f_45])).
% 24.67/16.93  tff(c_74, plain, (![A_102]: (m1_subset_1(A_102, u1_struct_0('#skF_4')) | ~r2_hidden(A_102, '#skF_7'))), inference(resolution, [status(thm)], [c_38, c_68])).
% 24.67/16.93  tff(c_1731, plain, (![A_316, D_317, C_318, B_319]: (r2_hidden('#skF_1'(k3_orders_2(A_316, D_317, C_318), B_319), D_317) | ~m1_subset_1(D_317, k1_zfmisc_1(u1_struct_0(A_316))) | ~m1_subset_1(C_318, u1_struct_0(A_316)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_316, D_317, C_318), B_319), u1_struct_0(A_316)) | ~l1_orders_2(A_316) | ~v5_orders_2(A_316) | ~v4_orders_2(A_316) | ~v3_orders_2(A_316) | v2_struct_0(A_316) | r1_tarski(k3_orders_2(A_316, D_317, C_318), B_319))), inference(resolution, [status(thm)], [c_6, c_286])).
% 24.67/16.93  tff(c_1734, plain, (![D_317, C_318, B_319]: (r2_hidden('#skF_1'(k3_orders_2('#skF_4', D_317, C_318), B_319), D_317) | ~m1_subset_1(D_317, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(C_318, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | r1_tarski(k3_orders_2('#skF_4', D_317, C_318), B_319) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_4', D_317, C_318), B_319), '#skF_7'))), inference(resolution, [status(thm)], [c_74, c_1731])).
% 24.67/16.93  tff(c_1740, plain, (![D_317, C_318, B_319]: (r2_hidden('#skF_1'(k3_orders_2('#skF_4', D_317, C_318), B_319), D_317) | ~m1_subset_1(D_317, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(C_318, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | r1_tarski(k3_orders_2('#skF_4', D_317, C_318), B_319) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_4', D_317, C_318), B_319), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_1734])).
% 24.67/16.93  tff(c_1741, plain, (![D_317, C_318, B_319]: (r2_hidden('#skF_1'(k3_orders_2('#skF_4', D_317, C_318), B_319), D_317) | ~m1_subset_1(D_317, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(C_318, u1_struct_0('#skF_4')) | r1_tarski(k3_orders_2('#skF_4', D_317, C_318), B_319) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_4', D_317, C_318), B_319), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_52, c_1740])).
% 24.67/16.93  tff(c_2884, plain, (![C_530, B_531]: (r2_hidden('#skF_1'(k3_orders_2('#skF_4', '#skF_7', C_530), B_531), '#skF_7') | ~m1_subset_1(C_530, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | r1_tarski(k3_orders_2('#skF_4', '#skF_7', C_530), B_531))), inference(resolution, [status(thm)], [c_2881, c_1741])).
% 24.67/16.93  tff(c_2905, plain, (![C_530, B_531]: (r2_hidden('#skF_1'(k3_orders_2('#skF_4', '#skF_7', C_530), B_531), '#skF_7') | ~m1_subset_1(C_530, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | r1_tarski(k3_orders_2('#skF_4', '#skF_7', C_530), B_531))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_38, c_2884])).
% 24.67/16.93  tff(c_2916, plain, (![C_532, B_533]: (r2_hidden('#skF_1'(k3_orders_2('#skF_4', '#skF_7', C_532), B_533), '#skF_7') | ~m1_subset_1(C_532, u1_struct_0('#skF_4')) | r1_tarski(k3_orders_2('#skF_4', '#skF_7', C_532), B_533))), inference(negUnitSimplification, [status(thm)], [c_52, c_2905])).
% 24.67/16.93  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 24.67/16.93  tff(c_2928, plain, (![C_532, B_533, B_2]: (r2_hidden('#skF_1'(k3_orders_2('#skF_4', '#skF_7', C_532), B_533), B_2) | ~r1_tarski('#skF_7', B_2) | ~m1_subset_1(C_532, u1_struct_0('#skF_4')) | r1_tarski(k3_orders_2('#skF_4', '#skF_7', C_532), B_533))), inference(resolution, [status(thm)], [c_2916, c_2])).
% 24.67/16.93  tff(c_61, plain, (![C_99, B_100, A_101]: (r2_hidden(C_99, B_100) | ~r2_hidden(C_99, A_101) | ~r1_tarski(A_101, B_100))), inference(cnfTransformation, [status(thm)], [f_32])).
% 24.67/16.93  tff(c_66, plain, (![A_1, B_2, B_100]: (r2_hidden('#skF_1'(A_1, B_2), B_100) | ~r1_tarski(A_1, B_100) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_61])).
% 24.67/16.93  tff(c_483, plain, (![A_185, B_186, C_187, D_188]: (r2_orders_2(A_185, B_186, C_187) | ~r2_hidden(B_186, k3_orders_2(A_185, D_188, C_187)) | ~m1_subset_1(D_188, k1_zfmisc_1(u1_struct_0(A_185))) | ~m1_subset_1(C_187, u1_struct_0(A_185)) | ~m1_subset_1(B_186, u1_struct_0(A_185)) | ~l1_orders_2(A_185) | ~v5_orders_2(A_185) | ~v4_orders_2(A_185) | ~v3_orders_2(A_185) | v2_struct_0(A_185))), inference(cnfTransformation, [status(thm)], [f_88])).
% 24.67/16.93  tff(c_7409, plain, (![D_931, B_929, A_927, C_928, A_930]: (r2_orders_2(A_927, '#skF_1'(A_930, B_929), C_928) | ~m1_subset_1(D_931, k1_zfmisc_1(u1_struct_0(A_927))) | ~m1_subset_1(C_928, u1_struct_0(A_927)) | ~m1_subset_1('#skF_1'(A_930, B_929), u1_struct_0(A_927)) | ~l1_orders_2(A_927) | ~v5_orders_2(A_927) | ~v4_orders_2(A_927) | ~v3_orders_2(A_927) | v2_struct_0(A_927) | ~r1_tarski(A_930, k3_orders_2(A_927, D_931, C_928)) | r1_tarski(A_930, B_929))), inference(resolution, [status(thm)], [c_66, c_483])).
% 24.67/16.93  tff(c_7415, plain, (![A_930, B_929, C_928]: (r2_orders_2('#skF_4', '#skF_1'(A_930, B_929), C_928) | ~m1_subset_1(C_928, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(A_930, B_929), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_930, k3_orders_2('#skF_4', '#skF_7', C_928)) | r1_tarski(A_930, B_929))), inference(resolution, [status(thm)], [c_38, c_7409])).
% 24.67/16.93  tff(c_7423, plain, (![A_930, B_929, C_928]: (r2_orders_2('#skF_4', '#skF_1'(A_930, B_929), C_928) | ~m1_subset_1(C_928, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(A_930, B_929), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~r1_tarski(A_930, k3_orders_2('#skF_4', '#skF_7', C_928)) | r1_tarski(A_930, B_929))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_7415])).
% 24.67/16.93  tff(c_7489, plain, (![A_941, B_942, C_943]: (r2_orders_2('#skF_4', '#skF_1'(A_941, B_942), C_943) | ~m1_subset_1(C_943, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(A_941, B_942), u1_struct_0('#skF_4')) | ~r1_tarski(A_941, k3_orders_2('#skF_4', '#skF_7', C_943)) | r1_tarski(A_941, B_942))), inference(negUnitSimplification, [status(thm)], [c_52, c_7423])).
% 24.67/16.93  tff(c_7517, plain, (![A_944, B_945, C_946]: (r2_orders_2('#skF_4', '#skF_1'(A_944, B_945), C_946) | ~m1_subset_1(C_946, u1_struct_0('#skF_4')) | ~r1_tarski(A_944, k3_orders_2('#skF_4', '#skF_7', C_946)) | r1_tarski(A_944, B_945) | ~r2_hidden('#skF_1'(A_944, B_945), '#skF_7'))), inference(resolution, [status(thm)], [c_74, c_7489])).
% 24.67/16.93  tff(c_1255, plain, (![B_261, C_263, D_260, E_264, A_262]: (r2_hidden(B_261, E_264) | ~m1_orders_2(E_264, A_262, D_260) | ~r2_hidden(C_263, E_264) | ~r2_hidden(B_261, D_260) | ~r2_orders_2(A_262, B_261, C_263) | ~m1_subset_1(E_264, k1_zfmisc_1(u1_struct_0(A_262))) | ~m1_subset_1(D_260, k1_zfmisc_1(u1_struct_0(A_262))) | ~m1_subset_1(C_263, u1_struct_0(A_262)) | ~m1_subset_1(B_261, u1_struct_0(A_262)) | ~l1_orders_2(A_262) | ~v5_orders_2(A_262) | ~v4_orders_2(A_262) | ~v3_orders_2(A_262) | v2_struct_0(A_262))), inference(cnfTransformation, [status(thm)], [f_164])).
% 24.67/16.93  tff(c_1257, plain, (![B_261, C_263]: (r2_hidden(B_261, '#skF_6') | ~r2_hidden(C_263, '#skF_6') | ~r2_hidden(B_261, '#skF_7') | ~r2_orders_2('#skF_4', B_261, C_263) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(C_263, u1_struct_0('#skF_4')) | ~m1_subset_1(B_261, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_1255])).
% 24.67/16.93  tff(c_1260, plain, (![B_261, C_263]: (r2_hidden(B_261, '#skF_6') | ~r2_hidden(C_263, '#skF_6') | ~r2_hidden(B_261, '#skF_7') | ~r2_orders_2('#skF_4', B_261, C_263) | ~m1_subset_1(C_263, u1_struct_0('#skF_4')) | ~m1_subset_1(B_261, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_38, c_40, c_1257])).
% 24.67/16.93  tff(c_1261, plain, (![B_261, C_263]: (r2_hidden(B_261, '#skF_6') | ~r2_hidden(C_263, '#skF_6') | ~r2_hidden(B_261, '#skF_7') | ~r2_orders_2('#skF_4', B_261, C_263) | ~m1_subset_1(C_263, u1_struct_0('#skF_4')) | ~m1_subset_1(B_261, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_1260])).
% 24.67/16.93  tff(c_23253, plain, (![A_1746, B_1747, C_1748]: (r2_hidden('#skF_1'(A_1746, B_1747), '#skF_6') | ~r2_hidden(C_1748, '#skF_6') | ~m1_subset_1('#skF_1'(A_1746, B_1747), u1_struct_0('#skF_4')) | ~m1_subset_1(C_1748, u1_struct_0('#skF_4')) | ~r1_tarski(A_1746, k3_orders_2('#skF_4', '#skF_7', C_1748)) | r1_tarski(A_1746, B_1747) | ~r2_hidden('#skF_1'(A_1746, B_1747), '#skF_7'))), inference(resolution, [status(thm)], [c_7517, c_1261])).
% 24.67/16.93  tff(c_23281, plain, (![A_1749, B_1750, C_1751]: (r2_hidden('#skF_1'(A_1749, B_1750), '#skF_6') | ~r2_hidden(C_1751, '#skF_6') | ~m1_subset_1(C_1751, u1_struct_0('#skF_4')) | ~r1_tarski(A_1749, k3_orders_2('#skF_4', '#skF_7', C_1751)) | r1_tarski(A_1749, B_1750) | ~r2_hidden('#skF_1'(A_1749, B_1750), '#skF_7'))), inference(resolution, [status(thm)], [c_74, c_23253])).
% 24.67/16.93  tff(c_23335, plain, (![C_1752, B_1753]: (r2_hidden('#skF_1'(k3_orders_2('#skF_4', '#skF_7', C_1752), B_1753), '#skF_6') | ~r2_hidden(C_1752, '#skF_6') | ~m1_subset_1(C_1752, u1_struct_0('#skF_4')) | r1_tarski(k3_orders_2('#skF_4', '#skF_7', C_1752), B_1753) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_4', '#skF_7', C_1752), B_1753), '#skF_7'))), inference(resolution, [status(thm)], [c_59, c_23281])).
% 24.67/16.93  tff(c_23371, plain, (![C_532, B_533]: (r2_hidden('#skF_1'(k3_orders_2('#skF_4', '#skF_7', C_532), B_533), '#skF_6') | ~r2_hidden(C_532, '#skF_6') | ~r1_tarski('#skF_7', '#skF_7') | ~m1_subset_1(C_532, u1_struct_0('#skF_4')) | r1_tarski(k3_orders_2('#skF_4', '#skF_7', C_532), B_533))), inference(resolution, [status(thm)], [c_2928, c_23335])).
% 24.67/16.93  tff(c_23437, plain, (![C_532, B_533]: (r2_hidden('#skF_1'(k3_orders_2('#skF_4', '#skF_7', C_532), B_533), '#skF_6') | ~r2_hidden(C_532, '#skF_6') | ~m1_subset_1(C_532, u1_struct_0('#skF_4')) | r1_tarski(k3_orders_2('#skF_4', '#skF_7', C_532), B_533))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_23371])).
% 24.67/16.93  tff(c_3683, plain, (![A_562, A_563, C_561, B_559, B_560]: (m1_subset_1('#skF_1'(A_562, B_560), u1_struct_0(A_563)) | ~m1_subset_1(C_561, u1_struct_0(A_563)) | ~m1_subset_1(B_559, k1_zfmisc_1(u1_struct_0(A_563))) | ~l1_orders_2(A_563) | ~v5_orders_2(A_563) | ~v4_orders_2(A_563) | ~v3_orders_2(A_563) | v2_struct_0(A_563) | ~r1_tarski(A_562, k3_orders_2(A_563, B_559, C_561)) | r1_tarski(A_562, B_560))), inference(resolution, [status(thm)], [c_66, c_1358])).
% 24.67/16.93  tff(c_3689, plain, (![A_562, B_560, C_561]: (m1_subset_1('#skF_1'(A_562, B_560), u1_struct_0('#skF_4')) | ~m1_subset_1(C_561, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(A_562, k3_orders_2('#skF_4', '#skF_7', C_561)) | r1_tarski(A_562, B_560))), inference(resolution, [status(thm)], [c_38, c_3683])).
% 24.67/16.93  tff(c_3697, plain, (![A_562, B_560, C_561]: (m1_subset_1('#skF_1'(A_562, B_560), u1_struct_0('#skF_4')) | ~m1_subset_1(C_561, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~r1_tarski(A_562, k3_orders_2('#skF_4', '#skF_7', C_561)) | r1_tarski(A_562, B_560))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_3689])).
% 24.67/16.93  tff(c_3924, plain, (![A_576, B_577, C_578]: (m1_subset_1('#skF_1'(A_576, B_577), u1_struct_0('#skF_4')) | ~m1_subset_1(C_578, u1_struct_0('#skF_4')) | ~r1_tarski(A_576, k3_orders_2('#skF_4', '#skF_7', C_578)) | r1_tarski(A_576, B_577))), inference(negUnitSimplification, [status(thm)], [c_52, c_3697])).
% 24.67/16.93  tff(c_3949, plain, (![C_578, B_577]: (m1_subset_1('#skF_1'(k3_orders_2('#skF_4', '#skF_7', C_578), B_577), u1_struct_0('#skF_4')) | ~m1_subset_1(C_578, u1_struct_0('#skF_4')) | r1_tarski(k3_orders_2('#skF_4', '#skF_7', C_578), B_577))), inference(resolution, [status(thm)], [c_59, c_3924])).
% 24.67/16.93  tff(c_73, plain, (![A_102]: (m1_subset_1(A_102, u1_struct_0('#skF_4')) | ~r2_hidden(A_102, '#skF_6'))), inference(resolution, [status(thm)], [c_40, c_68])).
% 24.67/16.93  tff(c_1885, plain, (![A_350, D_351, C_352, B_353]: (r2_orders_2(A_350, '#skF_1'(k3_orders_2(A_350, D_351, C_352), B_353), C_352) | ~m1_subset_1(D_351, k1_zfmisc_1(u1_struct_0(A_350))) | ~m1_subset_1(C_352, u1_struct_0(A_350)) | ~m1_subset_1('#skF_1'(k3_orders_2(A_350, D_351, C_352), B_353), u1_struct_0(A_350)) | ~l1_orders_2(A_350) | ~v5_orders_2(A_350) | ~v4_orders_2(A_350) | ~v3_orders_2(A_350) | v2_struct_0(A_350) | r1_tarski(k3_orders_2(A_350, D_351, C_352), B_353))), inference(resolution, [status(thm)], [c_6, c_483])).
% 24.67/16.93  tff(c_1891, plain, (![D_351, C_352, B_353]: (r2_orders_2('#skF_4', '#skF_1'(k3_orders_2('#skF_4', D_351, C_352), B_353), C_352) | ~m1_subset_1(D_351, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(C_352, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | r1_tarski(k3_orders_2('#skF_4', D_351, C_352), B_353) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_4', D_351, C_352), B_353), '#skF_6'))), inference(resolution, [status(thm)], [c_73, c_1885])).
% 24.67/16.93  tff(c_1898, plain, (![D_351, C_352, B_353]: (r2_orders_2('#skF_4', '#skF_1'(k3_orders_2('#skF_4', D_351, C_352), B_353), C_352) | ~m1_subset_1(D_351, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(C_352, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | r1_tarski(k3_orders_2('#skF_4', D_351, C_352), B_353) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_4', D_351, C_352), B_353), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_1891])).
% 24.67/16.93  tff(c_1899, plain, (![D_351, C_352, B_353]: (r2_orders_2('#skF_4', '#skF_1'(k3_orders_2('#skF_4', D_351, C_352), B_353), C_352) | ~m1_subset_1(D_351, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(C_352, u1_struct_0('#skF_4')) | r1_tarski(k3_orders_2('#skF_4', D_351, C_352), B_353) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_4', D_351, C_352), B_353), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_52, c_1898])).
% 24.67/16.93  tff(c_654, plain, (![B_208, A_209, D_210, C_211]: (r2_hidden(B_208, k3_orders_2(A_209, D_210, C_211)) | ~r2_hidden(B_208, D_210) | ~r2_orders_2(A_209, B_208, C_211) | ~m1_subset_1(D_210, k1_zfmisc_1(u1_struct_0(A_209))) | ~m1_subset_1(C_211, u1_struct_0(A_209)) | ~m1_subset_1(B_208, u1_struct_0(A_209)) | ~l1_orders_2(A_209) | ~v5_orders_2(A_209) | ~v4_orders_2(A_209) | ~v3_orders_2(A_209) | v2_struct_0(A_209))), inference(cnfTransformation, [status(thm)], [f_88])).
% 24.67/16.93  tff(c_658, plain, (![B_208, C_211]: (r2_hidden(B_208, k3_orders_2('#skF_4', '#skF_6', C_211)) | ~r2_hidden(B_208, '#skF_6') | ~r2_orders_2('#skF_4', B_208, C_211) | ~m1_subset_1(C_211, u1_struct_0('#skF_4')) | ~m1_subset_1(B_208, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_654])).
% 24.67/16.93  tff(c_664, plain, (![B_208, C_211]: (r2_hidden(B_208, k3_orders_2('#skF_4', '#skF_6', C_211)) | ~r2_hidden(B_208, '#skF_6') | ~r2_orders_2('#skF_4', B_208, C_211) | ~m1_subset_1(C_211, u1_struct_0('#skF_4')) | ~m1_subset_1(B_208, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_658])).
% 24.67/16.93  tff(c_1023, plain, (![B_246, C_247]: (r2_hidden(B_246, k3_orders_2('#skF_4', '#skF_6', C_247)) | ~r2_hidden(B_246, '#skF_6') | ~r2_orders_2('#skF_4', B_246, C_247) | ~m1_subset_1(C_247, u1_struct_0('#skF_4')) | ~m1_subset_1(B_246, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_664])).
% 24.67/16.93  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 24.67/16.93  tff(c_3964, plain, (![A_583, C_584]: (r1_tarski(A_583, k3_orders_2('#skF_4', '#skF_6', C_584)) | ~r2_hidden('#skF_1'(A_583, k3_orders_2('#skF_4', '#skF_6', C_584)), '#skF_6') | ~r2_orders_2('#skF_4', '#skF_1'(A_583, k3_orders_2('#skF_4', '#skF_6', C_584)), C_584) | ~m1_subset_1(C_584, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_1'(A_583, k3_orders_2('#skF_4', '#skF_6', C_584)), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1023, c_4])).
% 24.67/16.93  tff(c_34044, plain, (![D_2177, C_2178]: (~m1_subset_1('#skF_1'(k3_orders_2('#skF_4', D_2177, C_2178), k3_orders_2('#skF_4', '#skF_6', C_2178)), u1_struct_0('#skF_4')) | ~m1_subset_1(D_2177, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(C_2178, u1_struct_0('#skF_4')) | r1_tarski(k3_orders_2('#skF_4', D_2177, C_2178), k3_orders_2('#skF_4', '#skF_6', C_2178)) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_4', D_2177, C_2178), k3_orders_2('#skF_4', '#skF_6', C_2178)), '#skF_6'))), inference(resolution, [status(thm)], [c_1899, c_3964])).
% 24.67/16.93  tff(c_34056, plain, (![C_578]: (~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r2_hidden('#skF_1'(k3_orders_2('#skF_4', '#skF_7', C_578), k3_orders_2('#skF_4', '#skF_6', C_578)), '#skF_6') | ~m1_subset_1(C_578, u1_struct_0('#skF_4')) | r1_tarski(k3_orders_2('#skF_4', '#skF_7', C_578), k3_orders_2('#skF_4', '#skF_6', C_578)))), inference(resolution, [status(thm)], [c_3949, c_34044])).
% 24.67/16.93  tff(c_34085, plain, (![C_2179]: (~r2_hidden('#skF_1'(k3_orders_2('#skF_4', '#skF_7', C_2179), k3_orders_2('#skF_4', '#skF_6', C_2179)), '#skF_6') | ~m1_subset_1(C_2179, u1_struct_0('#skF_4')) | r1_tarski(k3_orders_2('#skF_4', '#skF_7', C_2179), k3_orders_2('#skF_4', '#skF_6', C_2179)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34056])).
% 24.67/16.93  tff(c_34181, plain, (![C_2180]: (~r2_hidden(C_2180, '#skF_6') | ~m1_subset_1(C_2180, u1_struct_0('#skF_4')) | r1_tarski(k3_orders_2('#skF_4', '#skF_7', C_2180), k3_orders_2('#skF_4', '#skF_6', C_2180)))), inference(resolution, [status(thm)], [c_23437, c_34085])).
% 24.67/16.93  tff(c_106, plain, (![A_119, B_120]: (r2_hidden('#skF_2'(A_119, B_120), B_120) | r2_hidden('#skF_3'(A_119, B_120), A_119) | B_120=A_119)), inference(cnfTransformation, [status(thm)], [f_39])).
% 24.67/16.93  tff(c_235, plain, (![A_155, B_156, B_157]: (r2_hidden('#skF_3'(A_155, B_156), B_157) | ~r1_tarski(A_155, B_157) | r2_hidden('#skF_2'(A_155, B_156), B_156) | B_156=A_155)), inference(resolution, [status(thm)], [c_106, c_2])).
% 24.67/16.93  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 24.67/16.93  tff(c_256, plain, (![A_158, B_159]: (~r1_tarski(A_158, B_159) | r2_hidden('#skF_2'(A_158, B_159), B_159) | B_159=A_158)), inference(resolution, [status(thm)], [c_235, c_10])).
% 24.67/16.93  tff(c_274, plain, (![A_160, B_161, B_162]: (r2_hidden('#skF_2'(A_160, B_161), B_162) | ~r1_tarski(B_161, B_162) | ~r1_tarski(A_160, B_161) | B_161=A_160)), inference(resolution, [status(thm)], [c_256, c_2])).
% 24.67/16.93  tff(c_94, plain, (![A_113, B_114]: (~r2_hidden('#skF_2'(A_113, B_114), A_113) | r2_hidden('#skF_3'(A_113, B_114), A_113) | B_114=A_113)), inference(cnfTransformation, [status(thm)], [f_39])).
% 24.67/16.93  tff(c_97, plain, (![A_113, B_114, B_2]: (r2_hidden('#skF_3'(A_113, B_114), B_2) | ~r1_tarski(A_113, B_2) | ~r2_hidden('#skF_2'(A_113, B_114), A_113) | B_114=A_113)), inference(resolution, [status(thm)], [c_94, c_2])).
% 24.67/16.93  tff(c_438, plain, (![B_179, B_180, B_181]: (r2_hidden('#skF_3'(B_179, B_180), B_181) | ~r1_tarski(B_179, B_181) | ~r1_tarski(B_180, B_179) | ~r1_tarski(B_179, B_180) | B_180=B_179)), inference(resolution, [status(thm)], [c_274, c_97])).
% 24.67/16.93  tff(c_8, plain, (![A_6, B_7]: (~r2_hidden('#skF_2'(A_6, B_7), A_6) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 24.67/16.93  tff(c_284, plain, (![B_162, B_161]: (~r2_hidden('#skF_3'(B_162, B_161), B_161) | ~r1_tarski(B_161, B_162) | ~r1_tarski(B_162, B_161) | B_162=B_161)), inference(resolution, [status(thm)], [c_274, c_8])).
% 24.67/16.93  tff(c_457, plain, (![B_181, B_179]: (~r1_tarski(B_181, B_179) | ~r1_tarski(B_179, B_181) | B_181=B_179)), inference(resolution, [status(thm)], [c_438, c_284])).
% 24.67/16.93  tff(c_36899, plain, (![C_2222]: (~r1_tarski(k3_orders_2('#skF_4', '#skF_6', C_2222), k3_orders_2('#skF_4', '#skF_7', C_2222)) | k3_orders_2('#skF_4', '#skF_7', C_2222)=k3_orders_2('#skF_4', '#skF_6', C_2222) | ~r2_hidden(C_2222, '#skF_6') | ~m1_subset_1(C_2222, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_34181, c_457])).
% 24.67/16.93  tff(c_36911, plain, (![B_38]: (k3_orders_2('#skF_4', '#skF_7', B_38)=k3_orders_2('#skF_4', '#skF_6', B_38) | ~r2_hidden(B_38, '#skF_6') | ~r1_tarski('#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_38, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_36899])).
% 24.67/16.93  tff(c_36916, plain, (![B_38]: (k3_orders_2('#skF_4', '#skF_7', B_38)=k3_orders_2('#skF_4', '#skF_6', B_38) | ~r2_hidden(B_38, '#skF_6') | ~m1_subset_1(B_38, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_40, c_38, c_126, c_36911])).
% 24.67/16.93  tff(c_37026, plain, (![B_2227]: (k3_orders_2('#skF_4', '#skF_7', B_2227)=k3_orders_2('#skF_4', '#skF_6', B_2227) | ~r2_hidden(B_2227, '#skF_6') | ~m1_subset_1(B_2227, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_52, c_36916])).
% 24.67/16.93  tff(c_37135, plain, (k3_orders_2('#skF_4', '#skF_7', '#skF_5')=k3_orders_2('#skF_4', '#skF_6', '#skF_5') | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_42, c_37026])).
% 24.67/16.93  tff(c_37192, plain, (k3_orders_2('#skF_4', '#skF_7', '#skF_5')=k3_orders_2('#skF_4', '#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_37135])).
% 24.67/16.93  tff(c_37194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_37192])).
% 24.67/16.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.67/16.93  
% 24.67/16.93  Inference rules
% 24.67/16.93  ----------------------
% 24.67/16.93  #Ref     : 0
% 24.67/16.93  #Sup     : 8618
% 24.67/16.93  #Fact    : 2
% 24.67/16.93  #Define  : 0
% 24.67/16.93  #Split   : 3
% 24.67/16.93  #Chain   : 0
% 24.67/16.94  #Close   : 0
% 24.67/16.94  
% 24.67/16.94  Ordering : KBO
% 24.67/16.94  
% 24.67/16.94  Simplification rules
% 24.67/16.94  ----------------------
% 24.67/16.94  #Subsume      : 3717
% 24.67/16.94  #Demod        : 4522
% 24.67/16.94  #Tautology    : 540
% 24.67/16.94  #SimpNegUnit  : 670
% 24.67/16.94  #BackRed      : 0
% 24.67/16.94  
% 24.67/16.94  #Partial instantiations: 0
% 24.67/16.94  #Strategies tried      : 1
% 24.67/16.94  
% 24.67/16.94  Timing (in seconds)
% 24.67/16.94  ----------------------
% 24.67/16.94  Preprocessing        : 0.36
% 24.67/16.94  Parsing              : 0.19
% 24.67/16.94  CNF conversion       : 0.03
% 24.67/16.94  Main loop            : 15.80
% 24.67/16.94  Inferencing          : 2.25
% 24.67/16.94  Reduction            : 2.04
% 24.67/16.94  Demodulation         : 1.39
% 24.67/16.94  BG Simplification    : 0.15
% 24.67/16.94  Subsumption          : 10.88
% 24.67/16.94  Abstraction          : 0.30
% 24.67/16.94  MUC search           : 0.00
% 24.67/16.94  Cooper               : 0.00
% 24.67/16.94  Total                : 16.21
% 24.67/16.94  Index Insertion      : 0.00
% 24.67/16.94  Index Deletion       : 0.00
% 24.67/16.94  Index Matching       : 0.00
% 24.67/16.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
